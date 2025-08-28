use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};
use std::io::{self, ErrorKind};

pub fn generate_tmp_ll_from_c<P: AsRef<Path>>(c_path: P) -> io::Result<PathBuf> {
    let c_path = c_path.as_ref();

    // Required sanity checks
    if !c_path.exists() {
        return Err(io::Error::new(
            ErrorKind::NotFound,
            format!("input file not found: {}", c_path.display()),
        ));
    }
    if !c_path.is_file() {
        return Err(io::Error::new(
            ErrorKind::InvalidInput,
            format!("input path is not a file: {}", c_path.display()),
        ));
    }

    // file stem (e.g. "foo" from "foo.c")
    let stem = c_path
        .file_stem()
        .and_then(|s| s.to_str())
        .ok_or_else(|| io::Error::new(ErrorKind::InvalidInput, "invalid input filename"))?;

    let now_nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| io::Error::new(ErrorKind::Other, format!("time error: {}", e)))?
        .as_nanos();
    let tmp_dir = std::env::current_dir()?;

    let out_ll = tmp_dir.join(format!("{}_{}.ll", stem, now_nanos));
    let out_ssa_ll = tmp_dir.join(format!("{}_{}.ssa.ll", stem, now_nanos));

    let clang_path = "/opt/homebrew/opt/llvm@17/bin/clang";
    let opt_path = "/opt/homebrew/opt/llvm@17/bin/opt";

    // Run clang:
    let clang_status = Command::new(clang_path)
        .arg("-S")
        .arg("-emit-llvm")
        .arg("-fno-discard-value-names")
        .arg("-Xclang")
        .arg("-disable-O0-optnone")
        .arg(c_path)
        .arg("-o")
        .arg(&out_ll)
        .status()?; // propagate I/O errors (e.g., executable not found)

    if !clang_status.success() {
        return Err(io::Error::new(
            ErrorKind::Other,
            format!("clang failed (exit code: {:?})", clang_status.code()),
        ));
    }

    // Run opt:
    // Note: Do NOT spawn via a shell. Passing "-passes=instcombine" as one argument is correct.
    let opt_status = Command::new(opt_path)
        .arg("-S")
        .arg("-passes=instcombine")
        .arg(&out_ll)
        .arg("-o")
        .arg(&out_ssa_ll)
        .status()?;

    if !opt_status.success() {
        return Err(io::Error::new(
            ErrorKind::Other,
            format!("opt failed (exit code: {:?})", opt_status.code()),
        ));
    }

    // Success: return path to the clang-generated temporary .ll file.
    Ok(out_ll)
}