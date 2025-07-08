use std::{path::Path, process::Command};
use crate::error::ExtractError;

/// Run Yosys on `verilog_path` to produce `smt2_path`.
/// Uses the “clean” pipeline so that only your output regs
/// appear in the resulting SMT-LIB2.
pub fn run_yosys(verilog_path: &Path, smt2_path: &Path, top_module_name: &str) -> Result<(), ExtractError> {
    let status = Command::new("yosys")
        .arg("-q")  // quiet
        .arg("-p")
        .arg(format!(
            "\
            read_verilog -pwires {}; \
            hierarchy -check -top {}; \
            proc; flatten; \
            opt_clean -purge; \
            write_smt2 -stdt -nomem -wires {}",
            verilog_path.display(),
            top_module_name,
            smt2_path.display()
        ))
        .status()?;

    if !status.success() {
        return Err(ExtractError::YosysFailed(format!(
            "yosys exited with {}",
            status
        )));
    }
    Ok(())
}

pub fn run_yosys_with_build(build_path: &Path) -> Result<(), ExtractError> {
    let status = Command::new("yosys")
        .arg("-q")  // quiet
        .arg("-s")
        .arg(format!(
            "{}", build_path.display()
        ))
        .status()?;

    if !status.success() {
        return Err(ExtractError::YosysFailed(format!(
            "yosys exited with {}",
            status
        )));
    }
    Ok(())
}
