//! Context-mixing compressor: bitwise predictor (PAQ/lpaq family) + binary arithmetic coder.
//! Deterministic integer arithmetic only, so compress and decompress agree on any machine.

const NH: usize = 11; // hashed contexts
const NCTX: usize = NH + 2; // + order-0 and order-1 direct
const NI: usize = NCTX * 2 + NH + 2 + 1; // two inputs per context + match (2) + bias

fn squash(d: i32) -> i32 {
    if d > 2047 {
        return 4095;
    }
    if d < -2047 {
        return 0;
    }
    const T: [i32; 33] = [
        1, 2, 3, 6, 10, 16, 27, 45, 73, 120, 194, 310, 488, 747, 1101, 1546, 2047, 2549, 2994, 3348, 3607, 3785, 3901, 3975,
        4022, 4050, 4068, 4079, 4085, 4089, 4092, 4093, 4094,
    ];
    let w = d & 127;
    let i = ((d >> 7) + 16) as usize;
    (T[i] * (128 - w) + T[i + 1] * w + 64) >> 7
}

struct Tables {
    stretch: Vec<i16>,
    dt: Vec<i32>,
}

impl Tables {
    fn new() -> Self {
        let mut stretch = vec![0i16; 4096];
        let mut pi = 0usize;
        for x in -2047..=2047 {
            let v = squash(x) as usize;
            for i in pi..=v {
                stretch[i] = x as i16;
            }
            pi = v + 1;
        }
        for i in pi..4096 {
            stretch[i] = 2047;
        }
        let dt = (0..1024).map(|n| (65536.0 / (n as f64 + 1.5)) as i32).collect();
        Tables { stretch, dt }
    }
}

#[inline]
fn hmix(a: u32, b: u32) -> u32 {
    (a.wrapping_mul(0x2F0B_4A27) ^ b.wrapping_mul(0x9E37_79B1)).rotate_left(13).wrapping_mul(0x85EB_CA6B)
}

struct Mixer {
    n: usize,
    w: Vec<i32>,
    sel: usize,
    pr: i32,
    lr: i32,
}

impl Mixer {
    fn new(n: usize, nsets: usize, init: i32, lr: i32) -> Self {
        Mixer { n, w: vec![init; n * nsets], sel: 0, pr: 2048, lr }
    }
    fn mix(&mut self, x: &[i32], sel: usize) -> i32 {
        self.sel = sel * self.n;
        let w = &self.w[self.sel..self.sel + self.n];
        let mut s: i64 = 0;
        for i in 0..self.n {
            s += x[i] as i64 * w[i] as i64;
        }
        let st = ((s >> 16) as i32).clamp(-2047, 2047);
        self.pr = squash(st);
        st
    }
    fn update(&mut self, x: &[i32], y: u32) {
        let err = ((y << 12) as i32 - self.pr) * self.lr;
        let w = &mut self.w[self.sel..self.sel + self.n];
        for i in 0..self.n {
            w[i] += (x[i] * err + (1 << 13)) >> 14;
        }
    }
}

struct Apm {
    t: Vec<u16>,
    idx: usize,
}

impl Apm {
    fn new(n: usize) -> Self {
        let mut t = vec![0u16; n * 24];
        for i in 0..n {
            for j in 0..24 {
                let s = (j as i32 * 4096) / 23 - 2048;
                t[i * 24 + j] = (squash(s) * 16) as u16;
            }
        }
        Apm { t, idx: 0 }
    }
    fn pp(&mut self, tb: &Tables, pr: i32, cx: usize) -> i32 {
        let s = (tb.stretch[pr as usize] as i32 + 2048) * 23;
        let wt = s & 0xfff;
        let base = cx * 24 + (s >> 12) as usize;
        self.idx = base + (wt >> 11) as usize;
        ((self.t[base] as i32 * (4096 - wt) + self.t[base + 1] as i32 * wt) >> 16).clamp(1, 4094)
    }
    fn update(&mut self, y: u32, rate: i32) {
        let g = ((y << 16) + (y << rate)) as i32 - y as i32 - y as i32;
        let v = self.t[self.idx] as i32;
        self.t[self.idx] = (v + ((g - v) >> rate)) as u16;
    }
}

pub struct Predictor {
    tb: Tables,
    bits: u32,
    tabs: Vec<Vec<u32>>,
    hist: Vec<Vec<u8>>,
    hsm: Vec<Vec<i32>>,
    t0: Vec<u32>,
    t1: Vec<u32>,
    hb: [u32; NH],
    idx: [usize; NH],
    i0: usize,
    i1: usize,
    c0: u32,
    bitpos: u32,
    c4: u32,
    c8: u32,
    word: u32,
    pword: u32,
    buf: Vec<u8>,
    ht: Vec<u32>,
    mh: u32,
    mlen: usize,
    mptr: usize,
    mm_sm: Vec<i32>,
    mm_idx: usize,
    inputs: [i32; NI],
    m1: Mixer,
    m2: Mixer,
    m3: Mixer,
    mf: Mixer,
    fin_in: [i32; 3],
    a1: Apm,
    a2: Apm,
    a3: Apm,
    pr: i32,
    pr_mix: i32,
    limit: u32,
    fw: (i32, i32, i32, i32),
}

const MINLEN: usize = 5;

// начальная оценка вероятности единицы по короткой истории битов (1 = пусто, дальше старший бит - маркер длины)
fn hist_init(st: usize) -> i32 {
    if st <= 1 {
        return 1 << 15;
    }
    let len = 63 - (st as u64).leading_zeros() as usize + 0;
    let len = len.min(5);
    let bits = st & ((1 << len) - 1);
    let ones = bits.count_ones() as i32;
    (((ones * 2 + 1) << 16) / (len as i32 * 2 + 2)).clamp(2000, 63000)
}

fn len_bucket(l: usize) -> usize {
    if l < 16 {
        l
    } else if l < 32 {
        16 + (l - 16) / 4
    } else if l < 64 {
        20 + (l - 32) / 8
    } else {
        (24 + (l - 64) / 64).min(31)
    }
}

impl Predictor {
    pub fn new(size_hint: usize) -> Self {
        let mut bits = 16u32;
        while bits < 24 && (1usize << bits) < size_hint.saturating_mul(16) {
            bits += 1;
        }
        let slot0: u32 = 1 << 31;
        let init = (65536 * 3) / 10;
        Predictor {
            tb: Tables::new(),
            bits,
            tabs: (0..NH).map(|_| vec![slot0; 1 << bits]).collect(),
            hist: (0..NH).map(|_| vec![1u8; 1 << bits]).collect(),
            hsm: (0..NH).map(|_| (0..64).map(|st| hist_init(st)).collect()).collect(),
            t0: vec![slot0; 256],
            t1: vec![slot0; 65536],
            hb: [0; NH],
            idx: [0; NH],
            i0: 0,
            i1: 0,
            c0: 1,
            bitpos: 0,
            c4: 0,
            c8: 0,
            word: 0,
            pword: 0,
            buf: Vec::with_capacity(size_hint),
            ht: vec![0; 1 << (bits.min(22))],
            mh: 0,
            mlen: 0,
            mptr: 0,
            mm_sm: vec![1 << 15; 64 * 2],
            mm_idx: usize::MAX,
            inputs: [0; NI],
            m1: Mixer::new(NI, 256, init, 10),
            m2: Mixer::new(NI, 33 * 8, init, 10),
            m3: Mixer::new(NI, 256 * 8, init, 10),
            mf: Mixer::new(3, 8, 65536 / 3, 2),
            fin_in: [0; 3],
            a1: Apm::new(256),
            a2: Apm::new(65536),
            a3: Apm::new(65536),
            pr: 2048,
            pr_mix: 2048,
            limit: 60,
            fw: (0, 4, 6, 6),
        }
    }

    fn slot_in(&self, s: u32, k: usize, inp: &mut [i32; NI]) {
        let n = s & 1023;
        if n == 0 {
            inp[k] = 0;
            inp[k + 1] = 0;
        } else {
            let p12 = (s >> 20) as usize;
            inp[k] = self.tb.stretch[p12] as i32;
            inp[k + 1] = (p12 as i32 - 2048) >> 1;
        }
    }

    pub fn p(&mut self) -> u32 {
        let c0 = self.c0;
        let bp = self.bitpos;
        let shift = 32 - self.bits;
        let mut inp = [0i32; NI];
        // hashed contexts
        for i in 0..NH {
            let h = hmix(self.hb[i], c0).wrapping_mul(0x9E37_79B1);
            self.idx[i] = (h >> shift) as usize;
            let s = self.tabs[i][self.idx[i]];
            self.slot_in(s, i * 2, &mut inp);
            let hs = self.hist[i][self.idx[i]] as usize;
            inp[NCTX * 2 + 3 + i] = if hs <= 1 { 0 } else { self.tb.stretch[(self.hsm[i][hs] >> 4).clamp(1, 4094) as usize] as i32 };
        }
        self.i0 = c0 as usize;
        self.i1 = (((self.c4 & 0xff) << 8) | c0) as usize;
        let s0 = self.t0[self.i0];
        let s1 = self.t1[self.i1];
        self.slot_in(s0, NH * 2, &mut inp);
        self.slot_in(s1, NH * 2 + 2, &mut inp);
        // match model
        let mk = NCTX * 2;  // за ним идут два входа совпадения и смещение, затем NH входов истории
        self.mm_idx = usize::MAX;
        let mut mlb = 0usize;
        if self.mlen > 0 {
            let e = self.buf[self.mptr] as u32;
            if ((e | 256) >> (8 - bp)) == c0 {
                let bit = (e >> (7 - bp)) & 1;
                let lb = len_bucket(self.mlen);
                mlb = 1 + lb;
                self.mm_idx = lb * 2 + bit as usize;
                let p = self.mm_sm[self.mm_idx] >> 4;
                inp[mk] = self.tb.stretch[(p as usize).clamp(1, 4094)] as i32;
                let conf = (self.mlen.min(32) as i32) * 32;
                inp[mk + 1] = if bit == 1 { conf } else { -conf };
            }
        }
        inp[mk + 2] = 256;
        // mixers
        let c1 = (self.c4 & 0xff) as usize;
        let s1m = self.m1.mix(&inp, c0 as usize);
        let s2m = self.m2.mix(&inp, mlb * 8 + bp as usize);
        let s3m = self.m3.mix(&inp, c1 * 8 + bp as usize);
        self.fin_in = [s1m, s2m, s3m];
        let sf = self.mf.mix(&self.fin_in, bp as usize);
        self.inputs = inp;
        let pm = squash(sf).clamp(1, 4094);
        self.pr_mix = pm;
        // APM / SSE chain
        let q1 = self.a1.pp(&self.tb, pm, c0 as usize);
        let c2 = ((self.c4 >> 8) & 0xff) as usize;
        let q2 = self.a2.pp(&self.tb, pm, (c1 << 8) | c0 as usize);
        let h3 = (hmix(self.c4 & 0xffffff, 77) >> 16) as usize;
        let q3 = self.a3.pp(&self.tb, pm, (h3 ^ ((c2 << 8) | c0 as usize)) & 0xffff);
        let _ = c2;
        let (wa, wb, wc, wd) = self.fw;
        let pr = (pm * wa + q1 * wb + q2 * wc + q3 * wd + 8) >> 4;
        self.pr = pr.clamp(1, 4095);
        self.pr as u32
    }

    fn upd_slot(&self, s: &mut u32, y: u32, limit: u32) {
        let n = *s & 1023;
        let p = (*s >> 10) as i32;
        let target = if y == 1 { (1 << 22) - 1 } else { 0 };
        let np = p + (((target - p) as i64 * self.tb.dt[n as usize] as i64) >> 16) as i32;
        let nn = if n < limit { n + 1 } else { n };
        *s = ((np as u32) << 10) | nn;
    }

    pub fn update(&mut self, y: u32) {
        // learn
        let lim = self.limit;
        for i in 0..NH {
            let mut s = self.tabs[i][self.idx[i]];
            self.upd_slot(&mut s, y, lim);
            self.tabs[i][self.idx[i]] = s;
            let hs = self.hist[i][self.idx[i]] as usize;
            let v = self.hsm[i][hs];
            self.hsm[i][hs] = v + (((y as i32) << 16) - v) / 96;
            let mut nh = (hs << 1) | y as usize;
            if nh >= 64 {
                nh = (nh & 31) | 32;
            }
            self.hist[i][self.idx[i]] = nh as u8;
        }
        let mut s = self.t0[self.i0];
        self.upd_slot(&mut s, y, 1023);
        self.t0[self.i0] = s;
        let mut s = self.t1[self.i1];
        self.upd_slot(&mut s, y, 1023);
        self.t1[self.i1] = s;
        if self.mm_idx != usize::MAX {
            let v = self.mm_sm[self.mm_idx];
            self.mm_sm[self.mm_idx] = v + (((y as i32) << 16) - v) / 64;
            // a wrong prediction ends the match for the rest of this byte
        }
        let inp = self.inputs;
        self.m1.update(&inp, y);
        self.m2.update(&inp, y);
        self.m3.update(&inp, y);
        let fi = self.fin_in;
        self.mf.update(&fi, y);
        self.a1.update(y, 7);
        self.a2.update(y, 7);
        self.a3.update(y, 7);
        // advance bit state
        self.c0 = (self.c0 << 1) | y;
        self.bitpos += 1;
        if self.bitpos == 8 {
            let c = (self.c0 & 0xff) as u8;
            self.byte_done(c);
            self.c0 = 1;
            self.bitpos = 0;
        }
    }

    fn byte_done(&mut self, c: u8) {
        self.buf.push(c);
        self.c8 = (self.c8 << 8) | (self.c4 >> 24);
        self.c4 = (self.c4 << 8) | c as u32;
        // word model: letters, digits and all bytes >= 128 (UTF-8)
        let is_w = c.is_ascii_alphanumeric() || c >= 128;
        if is_w {
            self.word = hmix(self.word.wrapping_add(c.to_ascii_lowercase() as u32 + 1), 0x5bd1_e995);
        } else if self.word != 0 {
            self.pword = self.word;
            self.word = 0;
        }
        let c4 = self.c4;
        let c8 = self.c8;
        self.hb[0] = hmix(1, c4 & 0xffff);
        self.hb[1] = hmix(2, c4 & 0xff_ffff);
        self.hb[2] = hmix(3, c4);
        self.hb[3] = hmix(hmix(4, c4), c8 & 0xffff);
        self.hb[4] = hmix(hmix(5, c4), c8);
        self.hb[5] = hmix(6, self.word);
        self.hb[6] = hmix(hmix(7, self.word), self.pword);
        self.hb[7] = hmix(8, (c4 >> 8) & 0xffff);
        self.hb[8] = hmix(9, (c4 & 0xff) | (((c4 >> 16) & 0xff) << 8));
        self.hb[9] = hmix(hmix(10, c4), c8 & 0xff);
        self.hb[10] = hmix(12, (c4 >> 8) & 0xff_ffff);
        // match model
        let n = self.buf.len();
        if self.mlen > 0 && self.buf[self.mptr] == c {
            self.mlen += 1;
            self.mptr += 1;
            if self.mlen > 65535 {
                self.mlen = 65535;
            }
        } else {
            self.mlen = 0;
        }
        if n >= MINLEN {
            let h = hmix(hmix(11, c4), c8 & 0xff) >> (32 - self.ht.len().trailing_zeros());
            self.mh = h;
            if self.mlen == 0 {
                let p = self.ht[h as usize] as usize;
                if p > 0 {
                    let mut l = 0usize;
                    while l < 400 && p > l && self.buf[p - 1 - l] == self.buf[n - 1 - l] {
                        l += 1;
                    }
                    if l >= MINLEN {
                        self.mlen = l;
                        self.mptr = p;
                    }
                }
            }
            self.ht[h as usize] = n as u32;
        }
    }
}

pub struct Encoder {
    x1: u32,
    x2: u32,
    pub out: Vec<u8>,
}

impl Encoder {
    pub fn new() -> Self {
        Encoder { x1: 0, x2: 0xffff_ffff, out: Vec::new() }
    }
    pub fn encode(&mut self, y: u32, p: u32) {
        let xmid = self.x1 + ((self.x2 - self.x1) >> 12) * p;
        if y == 1 {
            self.x2 = xmid;
        } else {
            self.x1 = xmid + 1;
        }
        while (self.x1 ^ self.x2) & 0xff00_0000 == 0 {
            self.out.push((self.x2 >> 24) as u8);
            self.x1 <<= 8;
            self.x2 = (self.x2 << 8) | 255;
        }
    }
    pub fn finish(mut self) -> Vec<u8> {
        let x = self.x1;
        self.out.extend_from_slice(&x.to_be_bytes());
        self.out
    }
}

pub struct Decoder<'a> {
    x1: u32,
    x2: u32,
    x: u32,
    data: &'a [u8],
    pos: usize,
}

impl<'a> Decoder<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        let mut d = Decoder { x1: 0, x2: 0xffff_ffff, x: 0, data, pos: 0 };
        for _ in 0..4 {
            d.x = (d.x << 8) | d.next() as u32;
        }
        d
    }
    fn next(&mut self) -> u8 {
        let b = self.data.get(self.pos).copied().unwrap_or(0);
        self.pos += 1;
        b
    }
    pub fn decode(&mut self, p: u32) -> u32 {
        let xmid = self.x1 + ((self.x2 - self.x1) >> 12) * p;
        let y = if self.x <= xmid {
            self.x2 = xmid;
            1
        } else {
            self.x1 = xmid + 1;
            0
        };
        while (self.x1 ^ self.x2) & 0xff00_0000 == 0 {
            self.x1 <<= 8;
            self.x2 = (self.x2 << 8) | 255;
            self.x = (self.x << 8) | self.next() as u32;
        }
        y
    }
}

pub fn compress(data: &[u8]) -> Vec<u8> {
    let mut pr = Predictor::new(data.len());
    let mut enc = Encoder::new();
    for &c in data {
        for i in (0..8).rev() {
            let y = ((c >> i) & 1) as u32;
            let p = pr.p();
            enc.encode(y, p);
            pr.update(y);
        }
    }
    enc.finish()
}

pub fn decompress(data: &[u8], n: usize) -> Vec<u8> {
    let mut pr = Predictor::new(n);
    let mut dec = Decoder::new(data);
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let mut c = 0u32;
        for _ in 0..8 {
            let p = pr.p();
            let y = dec.decode(p);
            pr.update(y);
            c = (c << 1) | y;
        }
        out.push(c as u8);
    }
    out
}
