mod error;
mod yosys;
mod parser;
mod model;
mod smt_preprocess;
mod ir_parser;

pub use error::ExtractError;
pub use model::{Model, RegisterInfo, VarType};

use z3::{Context};

use std::path::Path;
use ir::{SMVEnv};

pub fn build_smvenv_from_verilog<'ctx>(
    _build_file_path: &Path,
    top_module_name: &str,
    smt_path: &Path,
    context: &'ctx Context
) -> Result<SMVEnv<'ctx>, ExtractError> {

    yosys::run_yosys_with_build(_build_file_path)?;
    let smt_text = std::fs::read_to_string(&smt_path)?;
    let id_to_name = parser::parse_variables(&smt_text, top_module_name)?;
    let restored_smt2 = parser::restore_variable_names(&smt_text, &id_to_name);

    // Save restored SMT2 for debugging
    let restored_path = smt_path.with_file_name(format!("{}_restored.smt2", top_module_name));
    std::fs::write(&restored_path, &restored_smt2)
        .map_err(|e| ExtractError::Io(std::io::Error::new(
            std::io::ErrorKind::Other,
            format!("Failed to write restored SMT2 to {}: {}", restored_path.display(), e),
        )))?;

    let transformed_smt = smt_preprocess::transform(&restored_smt2);

    let transformed_path = smt_path.with_file_name(format!("{}_transformed.smt2", top_module_name));
    std::fs::write(&transformed_path, &transformed_smt)
        .map_err(|e| ExtractError::Io(std::io::Error::new(
            std::io::ErrorKind::Other,
            format!("Failed to write transformed SMT2 to {}: {}", transformed_path.display(), e),
        )))?;

    // Convert String -> ExtractError here:
    let env = ir_parser::build_env_from_flat_smt(context, &transformed_smt)
        .map_err(|e| ExtractError::Parse(format!("IR parse error: {e}")))?;  // <-- Pick the right variant name

    Ok(env)
}
