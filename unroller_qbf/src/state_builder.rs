use regex::Regex;
use std::collections::{HashMap, BTreeMap};
use std::fs::File;
use std::io::{self, BufRead, BufReader, Write};

// Parses the QCIR mapping file (qcir.txt) into a map from index to variable name
fn parse_mapping(mapping_file: &str) -> io::Result<HashMap<i32, String>> {
    let file = File::open(mapping_file)?;
    let reader = BufReader::new(file);
    let re = Regex::new(r"^#\s*(\d+)\s*:\s*(\S+)").unwrap();
    let mut mapping = HashMap::new();
    for line in reader.lines() {
        let line = line?;
        if let Some(caps) = re.captures(&line) {
            let idx: i32 = caps[1].parse().unwrap();
            let var = caps[2].to_string();
            mapping.insert(idx, var);
        }
    }
    Ok(mapping)
}

// Parses the QUABS assignment file (quabs.txt) to extract literals
fn parse_assignment(assignment_file: &str) -> io::Result<Vec<i32>> {
    let file = File::open(assignment_file)?;
    let reader = BufReader::new(file);
    let mut literals = Vec::new();
    for line in reader.lines() {
        let line = line?;
        let trimmed = line.trim();
        if trimmed.is_empty() || !trimmed.to_uppercase().starts_with('V') {
            continue;
        }
        let parts: Vec<&str> = trimmed.split_whitespace().collect();
        for &lit_str in &parts[1..] {
            if lit_str == "0" {
                break;
            }
            if let Ok(lit) = lit_str.parse() {
                literals.push(lit);
            }
        }
    }
    Ok(literals)
}

// Holds boolean and bit-blast groups for a single time step
#[derive(Default)]
struct StepData {
    bools: BTreeMap<String, bool>,
    bits: HashMap<String, HashMap<usize, bool>>,
}

// Builds the trace grouped by time step, reconstructing integers from bit-blasted bits
fn build_trace(mapping: &HashMap<i32, String>, literals: &[i32]) -> BTreeMap<usize, StepData> {
    let mut trace: BTreeMap<usize, StepData> = BTreeMap::new();
    let ts_re = Regex::new(r"(.+)\[(\d+)\]$").unwrap();

    for &lit in literals {
        let idx = lit.abs();
        let val = lit > 0;
        let var_full = mapping.get(&idx)
            .cloned()
            .unwrap_or_else(|| format!("var_{}", idx));

        if let Some(caps) = ts_re.captures(&var_full) {
            let var_no_ts = caps[1].to_string();
            let step: usize = caps[2].parse().unwrap();
            let parts: Vec<&str> = var_no_ts.split('_').collect();

            // Detect bit-blasted fields
            let num_idxs: Vec<usize> = parts.iter().enumerate()
                .filter(|(_, p)| p.chars().all(|c| c.is_ascii_digit()))
                .map(|(i, _)| i)
                .collect();

            let step_data = trace.entry(step).or_default();
            if let Some(&bit_pos) = num_idxs.first() {
                // It's a bit-blasted variable
                let bit_index: usize = parts[bit_pos].parse().unwrap();
                let base_name = parts.iter().enumerate()
                    .filter(|(i, _)| *i != bit_pos)
                    .map(|(_, &p)| p)
                    .collect::<Vec<_>>()
                    .join("_");

                let bit_map = step_data.bits.entry(base_name).or_default();
                bit_map.insert(bit_index, val);
            } else {
                // Plain boolean
                step_data.bools.insert(var_no_ts, val);
            }
        }
    }

    trace
}

fn main() -> io::Result<()> {
    // Parse inputs
    let mapping = parse_mapping("qcir.txt")?;
    let literals = parse_assignment("quabs.txt")?;

    // Build and write trace to states.txt
    let trace = build_trace(&mapping, &literals);
    let mut output = File::create("states.txt")?;

    for (step, data) in trace {
        writeln!(output, "## Step {}", step)?;

        // Print booleans
        for (name, &val) in &data.bools {
            writeln!(output, "{} = {}", name, val)?;
        }

        // Reassemble bit-blasted groups into integers
        let mut bases: Vec<&String> = data.bits.keys().collect();
        bases.sort();
        for &base in &bases {
            let bits_map = &data.bits[base];
            let mut indices: Vec<usize> = bits_map.keys().cloned().collect();
            indices.sort();

            let value: usize = indices.iter()
                .filter(|&&i| bits_map.get(&i).copied().unwrap_or(false))
                .map(|&i| 1 << i)
                .sum();

            let bit_str = indices.iter()
                .map(|&i| format!("{}:{}", i, bits_map[&i] as usize))
                .collect::<Vec<_>>()
                .join(",");

            writeln!(output, "{} = {}  # bits: {}", base, value, bit_str)?;
        }

        writeln!(output)?;
    }

    Ok(())
}

// Note: Add `regex = "1"` to your Cargo.toml dependencies to use the regex crate.
