mod cm;

use std::fs;
use std::io::Write;
use std::path::{Component, Path, PathBuf};
use std::process::Command;
use std::time::Instant;

fn put_varint(out: &mut Vec<u8>, mut v: u64) {
    while v >= 128 {
        out.push((v as u8 & 127) | 128);
        v >>= 7;
    }
    out.push(v as u8);
}

fn get_varint(d: &[u8], pos: &mut usize) -> Result<u64, String> {
    let mut v = 0u64;
    let mut s = 0;
    loop {
        let b = *d.get(*pos).ok_or("обрезанный файл")?;
        *pos += 1;
        v |= ((b & 127) as u64) << s;
        if b < 128 {
            return Ok(v);
        }
        s += 7;
        if s > 63 {
            return Err("плохое число".into());
        }
    }
}

fn crc32(d: &[u8]) -> u32 {
    let mut t = [0u32; 256];
    for i in 0..256u32 {
        let mut c = i;
        for _ in 0..8 {
            c = if c & 1 == 1 { 0xEDB8_8320 ^ (c >> 1) } else { c >> 1 };
        }
        t[i as usize] = c;
    }
    let mut c = !0u32;
    for &b in d {
        c = t[((c ^ b as u32) & 0xff) as usize] ^ (c >> 8);
    }
    !c
}

/// Поток: "RBP1", длина, crc, сжатые данные.
fn pack_stream(data: &[u8]) -> Vec<u8> {
    let mut out = b"RBP1".to_vec();
    put_varint(&mut out, data.len() as u64);
    out.extend_from_slice(&crc32(data).to_le_bytes());
    out.extend_from_slice(&cm::compress(data));
    out
}

fn unpack_stream(d: &[u8]) -> Result<Vec<u8>, String> {
    if d.len() < 9 || &d[..4] != b"RBP1" {
        return Err("это не архив rpack".into());
    }
    let mut pos = 4;
    let n = get_varint(d, &mut pos)? as usize;
    if n > (1usize << 34) {
        return Err("неправдоподобный размер".into());
    }
    let crc = u32::from_le_bytes(d.get(pos..pos + 4).ok_or("обрезанный файл")?.try_into().unwrap());
    pos += 4;
    let out = cm::decompress(&d[pos..], n);
    if crc32(&out) != crc {
        return Err("контрольная сумма не сошлась: архив повреждён".into());
    }
    Ok(out)
}

fn collect(path: &Path, base: &Path, out: &mut Vec<(String, PathBuf)>) -> Result<(), String> {
    let md = fs::metadata(path).map_err(|e| format!("{}: {e}", path.display()))?;
    if md.is_dir() {
        let mut ents: Vec<_> = fs::read_dir(path).map_err(|e| e.to_string())?.filter_map(|e| e.ok()).collect();
        ents.sort_by_key(|e| e.file_name());
        for e in ents {
            collect(&e.path(), base, out)?;
        }
    } else {
        let rel = path.strip_prefix(base).unwrap_or(path);
        let name = rel.components().filter_map(|c| if let Component::Normal(s) = c { s.to_str() } else { None }).collect::<Vec<_>>().join("/");
        out.push((name, path.to_path_buf()));
    }
    Ok(())
}

fn ext_of(name: &str) -> &str {
    name.rsplit_once('.').map(|x| x.1).unwrap_or("")
}

fn cmd_add(out: &str, paths: &[String]) -> Result<(), String> {
    let mut files = Vec::new();
    for p in paths {
        let pp = Path::new(p);
        let base = if pp.is_dir() { pp.parent().unwrap_or(Path::new("")).to_path_buf() } else { pp.parent().unwrap_or(Path::new("")).to_path_buf() };
        collect(pp, &base, &mut files)?;
    }
    // похожие файлы рядом: для сплошного (solid) сжатия это даёт заметный выигрыш
    files.sort_by(|a, b| ext_of(&a.0).cmp(ext_of(&b.0)).then(a.0.cmp(&b.0)));
    let mut hdr = Vec::new();
    let mut body = Vec::new();
    put_varint(&mut hdr, files.len() as u64);
    for (name, path) in &files {
        let data = fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
        put_varint(&mut hdr, name.len() as u64);
        hdr.extend_from_slice(name.as_bytes());
        put_varint(&mut hdr, data.len() as u64);
        body.extend_from_slice(&data);
    }
    let mut all = b"RBPK".to_vec();
    all.extend_from_slice(&hdr);
    all.extend_from_slice(&body);
    let t = Instant::now();
    let packed = pack_stream(&all);
    fs::write(out, &packed).map_err(|e| e.to_string())?;
    println!("{} файлов, {} -> {} байт ({:.2}x), {:.1} с", files.len(), body.len(), packed.len(), body.len() as f64 / packed.len() as f64, t.elapsed().as_secs_f64());
    Ok(())
}

fn safe_rel(name: &str) -> bool {
    !name.is_empty() && !name.starts_with('/') && !name.contains('\\') && !name.contains(':') && name.split('/').all(|c| !c.is_empty() && c != "." && c != "..")
}

fn cmd_extract(inp: &str, outdir: &str) -> Result<(), String> {
    let d = fs::read(inp).map_err(|e| e.to_string())?;
    let all = unpack_stream(&d)?;
    if all.len() < 4 || &all[..4] != b"RBPK" {
        return Err("в потоке нет списка файлов (это одиночный файл? используйте d)".into());
    }
    let mut pos = 4;
    let n = get_varint(&all, &mut pos)? as usize;
    let mut list = Vec::new();
    for _ in 0..n {
        let l = get_varint(&all, &mut pos)? as usize;
        let name = String::from_utf8(all.get(pos..pos + l).ok_or("обрезанный файл")?.to_vec()).map_err(|_| "имя не в UTF-8")?;
        pos += l;
        let sz = get_varint(&all, &mut pos)? as usize;
        list.push((name, sz));
    }
    for (name, sz) in list {
        if !safe_rel(&name) {
            return Err(format!("небезопасный путь в архиве: {name}"));
        }
        let data = all.get(pos..pos + sz).ok_or("обрезанный файл")?;
        pos += sz;
        let dest = Path::new(outdir).join(&name);
        if let Some(p) = dest.parent() {
            fs::create_dir_all(p).map_err(|e| e.to_string())?;
        }
        fs::write(&dest, data).map_err(|e| e.to_string())?;
    }
    println!("распаковано {n} файлов в {outdir}");
    Ok(())
}

fn external(cmd: &str, args: &[&str], data: &[u8]) -> Option<usize> {
    let tmp = std::env::temp_dir().join(format!("rpack_bench_{}", std::process::id()));
    fs::write(&tmp, data).ok()?;
    let out = Command::new(cmd).args(args).arg("-c").arg(&tmp).output().ok()?;
    let _ = fs::remove_file(&tmp);
    if out.status.success() {
        Some(out.stdout.len())
    } else {
        None
    }
}

fn cmd_bench(files: &[String]) -> Result<(), String> {
    println!("{:<28} {:>10} {:>9} {:>9} {:>9} {:>9} {:>7}", "файл", "размер", "gzip -9", "bzip2 -9", "xz -9e", "rpack", "сек");
    let (mut tot, mut tr) = (0usize, 0usize);
    for f in files {
        let data = fs::read(f).map_err(|e| format!("{f}: {e}"))?;
        let t = Instant::now();
        let packed = pack_stream(&data);
        let secs = t.elapsed().as_secs_f64();
        let back = unpack_stream(&packed)?;
        if back != data {
            return Err(format!("{f}: РАЗВАЛИЛОСЬ, распаковка не совпала"));
        }
        let g = external("gzip", &["-9"], &data);
        let b = external("bzip2", &["-9"], &data);
        let x = external("xz", &["-9e"], &data);
        let fmt = |v: Option<usize>| v.map(|n| n.to_string()).unwrap_or("-".into());
        let name = Path::new(f).file_name().and_then(|s| s.to_str()).unwrap_or(f);
        println!("{:<28} {:>10} {:>9} {:>9} {:>9} {:>9} {:>7.1}", name, data.len(), fmt(g), fmt(b), fmt(x), packed.len(), secs);
        tot += data.len();
        tr += packed.len();
    }
    println!("итого {} -> {} ({:.2}x); распаковка проверена побайтно", tot, tr, tot as f64 / tr as f64);
    Ok(())
}

fn run() -> Result<(), String> {
    let a: Vec<String> = std::env::args().collect();
    let usage = "rpack — архиватор со смешиванием контекстов\n  rpack c <файл> <выход>       сжать один файл\n  rpack d <вход> <выход>       распаковать один файл\n  rpack a <архив> <пути...>    упаковать файлы и папки (сплошной архив)\n  rpack x <архив> <папка>      распаковать архив\n  rpack bench <файлы...>       сравнить с gzip/bzip2/xz и проверить распаковку";
    match a.get(1).map(|s| s.as_str()) {
        Some("c") if a.len() == 4 => {
            let data = fs::read(&a[2]).map_err(|e| e.to_string())?;
            let p = pack_stream(&data);
            fs::write(&a[3], &p).map_err(|e| e.to_string())?;
            println!("{} -> {} байт ({:.2}x)", data.len(), p.len(), data.len() as f64 / p.len().max(1) as f64);
            Ok(())
        }
        Some("d") if a.len() == 4 => {
            let d = fs::read(&a[2]).map_err(|e| e.to_string())?;
            fs::write(&a[3], unpack_stream(&d)?).map_err(|e| e.to_string())
        }
        Some("a") if a.len() >= 4 => cmd_add(&a[2], &a[3..]),
        Some("x") if a.len() == 4 => cmd_extract(&a[2], &a[3]),
        Some("bench") if a.len() >= 3 => cmd_bench(&a[2..]),
        _ => {
            let _ = writeln!(std::io::stderr(), "{usage}");
            Err("неверные аргументы".into())
        }
    }
}

fn main() {
    if let Err(e) = run() {
        eprintln!("ошибка: {e}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_various() {
        let mut noise = Vec::new();
        let mut x = 12345u32;
        for _ in 0..5000 {
            x = x.wrapping_mul(1664525).wrapping_add(1013904223);
            noise.push((x >> 24) as u8);
        }
        let cases: Vec<Vec<u8>> = vec![vec![], vec![7], b"abcabcabcabc".repeat(500), noise, "привет, мир! ".repeat(300).into_bytes()];
        for c in cases {
            assert_eq!(unpack_stream(&pack_stream(&c)).unwrap(), c);
        }
    }

    #[test]
    fn rejects_unsafe_paths() {
        assert!(!safe_rel("../x"));
        assert!(!safe_rel("/etc/passwd"));
        assert!(!safe_rel("a\\b"));
        assert!(safe_rel("dir/file.txt"));
    }
}
