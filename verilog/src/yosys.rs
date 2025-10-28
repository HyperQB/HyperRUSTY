use std::{path::Path, process::Command};
use crate::error::ExtractError;

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
