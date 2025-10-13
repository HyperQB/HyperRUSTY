use regex::Regex;
use std::collections::HashMap;
use crate::error::ExtractError;

#[derive(Debug, Clone)]
pub struct VariableAlias {
    pub original_name: String,
    pub yosys_name: String,
}

#[derive(Debug, Clone)]
pub struct SMTVariables {
    pub name: String,
    pub var_type: String,
    pub getter: String,
}

/// Unrolls the design in-place, modifying the SMT2 string to include unrolling constraints.
/// Returns the modified SMT2 string, a list of states' names, and the mapping of the getters
pub fn unroll_in_place(smt2: &str, mod_name: &str, bound: usize, trace_id: &str, variable_filter: Option<Vec<String>>) -> Result<(String, Vec<String>, HashMap<String, String>), ExtractError> {
    // Parse the variables to get their names
    let id_to_name = parse_variables(smt2, mod_name)?;
    // Restore variable names in the SMT2 string
    let restored_smt2 = restore_variable_names(smt2, &id_to_name);
    let getter_map = map_variables(mod_name, &id_to_name);
    let smt_vars = collect_smt_vars(&restored_smt2);
    // Augment the SMT2 with unrolling logic
    let (unrolled_smt, state_names) = add_unrolling_constraints(&restored_smt2, mod_name, bound, trace_id, smt_vars, variable_filter);
    // Write to file
    let output_path = format!("{}_unrolled.smt2", mod_name);
    std::fs::write(&output_path, &unrolled_smt)
        .map_err(|e| ExtractError::Io(std::io::Error::new(std::io::ErrorKind::Other, format!("Failed to write unrolled SMT2 to {}: {}", output_path, e))))?;
    Ok((unrolled_smt, state_names, getter_map))
}

pub fn parse_variables(smt2: &str, mod_name: &str) -> Result<Vec<VariableAlias>, ExtractError> {
    let re = Regex::new(&format!(r"\s*\(\|({}#\d+)\|.*(Bool|BitVec).*;\s*\\(.*)[\r\n]", mod_name)).unwrap();
    let mut variables = Vec::new();
    for cap in re.captures_iter(smt2) {
        let yosys_name = cap[1].to_string();
        let original_name: String = cap[3]
            .chars()
            .map(|c| {
                if c.is_alphanumeric() || c == '.' || c == '_' {
                    c
                }else {
                    '_'
                }
            })
            .collect();
        variables.push(VariableAlias {
            original_name: original_name.clone(),
            yosys_name,
        });
    }
    if variables.is_empty() {
        println!("{:#?}", smt2);
        return Err(ExtractError::Parse(format!("No variables found for module {}", mod_name)));
    }
    Ok(variables)
}

pub fn restore_variable_names(smt2: &str, vars: &Vec<VariableAlias>) -> String {
    let mut result = smt2.to_string();
    for var in vars {
        let re = Regex::new(&format!(r"\|{}\|", var.yosys_name)).unwrap();
        result = re.replace_all(&result, format!("|{}|", var.original_name)).to_string();
    }
    result
}

// Maps each state variable's original name to its getter function name
// e.g. "PC" -> "|main_n PC|"
fn map_variables(mod_name: &str, variable_names: &Vec<VariableAlias>) -> HashMap<String, String> {
    let mut getter_map = HashMap::new();
    for var in variable_names {
        let getter_name = format!("|{}_n {}|", mod_name, var.original_name);
        getter_map.insert(var.original_name.clone(), getter_name);
    }
    getter_map
}

fn collect_smt_vars(smt2: &str) -> Vec<SMTVariables> {
    let re = Regex::new(r"\(define-fun (\|\S*_n ([^\$\s]*)\|) \(\S*\s\S*\) (Bool|\(_ BitVec \d+\))").unwrap();
    let mut variables = Vec::new();
    for cap in re.captures_iter(smt2) {
        let name = cap[2].to_string();
        let var_type = cap[3].to_string();
        let getter = cap[1].to_string();
        variables.push(SMTVariables {
            name,
            var_type,
            getter,
        });
    }
    //println!("Collected SMT Variables: {:#?}", variables);
    variables
}

// Augments the SMT2 string with unrolling constraints
// Returns the modified SMT2 string and a list of states' names
fn add_unrolling_constraints(smt2: &str, mod_name: &str, bound: usize, trace_id: &str, smt_vars: Vec<SMTVariables>, var_filter: Option<Vec<String>>) -> (String, Vec<String>) {
    let mut result = smt2.to_string();
    // Add constraints for unrolling
    
    //Variable probes
    // Here is where we would add a filter for which variables to probe
    // Vector of tuples (probe_name, state_name, var_getter, time_step)
    let mut probe_assertions: Vec<String> = Vec::new();
    for var in &smt_vars {
        if let Some(ref filter) = var_filter {
            if !filter.contains(&var.name) {
                continue;
            }
        }
        result.push_str(&format!(
            "\n; Probes for variable {}\n",
            var.name
        ));
        for i in 0..bound+1 {
            let probe_name = format!("|probe_{}_{}_{}|", var.name, trace_id, i);
            result.push_str(&format!(
                "(declare-const {} {})\n",
                probe_name,
                var.var_type
            ));
            let clause = format!(
                "(= {} ({} {}))",
                probe_name,
                var.getter,
                format!("s_{}_{}", trace_id, i)
            );
            //probe_assertions.push(clause);
        }
    }
    //println!("Probe assertions: {:#?}", probe_assertions);
    
    // State unrolling
    //Add contants for each step
    result.push_str(&format!(
        "\n; Unrolled states\n"
    ));
    let mut state_names = Vec::new();
    for i in 0..bound+1 {
        result.push_str(&format!(
            "(declare-const |s_{}_{}| |{}_s|)\n",
            trace_id,
            i,
            mod_name
        ));
        state_names.push(format!("|s_{}_{}|", trace_id, i));
    }
    // Add next-state constraints
    result.push_str(&format!(
        "\n; Initial and Next-state constraints\n"
    ));

    result.push_str(&format!(
        "(assert (and (|{}_i| |s_{}_0|) ",
        mod_name,
        trace_id 
    ));

    for i in 0..(bound) {
        result.push_str(&format!(
            "(|{}_t| s_{}_{} s_{}_{}) ",
            mod_name,
            trace_id,
            i,
            trace_id,
            i + 1
        ));
    }
    // Add probe assertions
    for assertion in probe_assertions {
        result.push_str(&format!("{} ", assertion));
    }
    result.push_str("))\n");

    result.push_str(&format!(
        "; End of unrolling constraints\n"
    ));
    (result, state_names)
}