# HyperQB 2.0



## Build HyperQB 2.0 from Source Code

### Rust

HyperQB 2.0 is implemented in Rust and uses Cargo for builds and execution. Please install the stable Rust toolchain (tested with `cargo 1.91.0`) via [rustup](https://rustup.rs/) or your package manager. Verify your setup with:

```bash
cargo --version
rustc --version
```

To check if HyperQB 2.0 compiled without error, execute: 
```bash
cargo build --release
``` 

### A first example

To test if HyperQB (SMT unrolling) can successfully compiled 

```bash
cargo run --release -- -n benchmarks/sync/0_infoflow/info.smv benchmarks/sync/0_infoflow/info.smv -f benchmarks/sync/0_infoflow/info.hq -k 10 -s hpes
```
which should return `result: sat` 

### Additional Dependencies for QBF solving and Verilog inputs

For quick trials we ship a release binary tested on `macOS M1` of `quabs` (that is, if you are on MacOS, you are ready to run QBF unrolling with `-q` flag, see "A second example"). 

- **Yosys:** required when using Verilog inputs via `-v`. Install Yosys (e.g., from your package manager or YosysHQ builds) and ensure the `yosys` binary is on `PATH`, because HyperQB invokes it to produce SMT from the Verilog build scripts.
- **NuSMV:** required when enabling QBF solving with `-q`. Install NuSMV and add its executable to `PATH` so HyperQB can parse NuSMV models and hand them to the QBF backend.
- **QuAbs:** the QBF mode expects the `quabs` binary (https://github.com/ltentrup/quabs) to live in the repository root. Build QuAbs per its instructions and copy the executable to the project’s top-level directory so `cargo run … -q` can invoke it directly.
  
  
### A second example

To test if HyperQB (QBF unrolling with `quabs`) can successfully run: 

```bash
cargo run --release -- -n benchmarks/sync/0_infoflow/info.smv benchmarks/sync/0_infoflow/info.smv -f benchmarks/sync/0_infoflow/info.hq -k 10 -s hpes -q
```
which should return `SAT`


### A third example

To test if HyoerQB (with verilog input using `yosys`) can successfully run:
```bash
cargo run --release -- -v benchmarks/verilog/divider/divider.ys benchmarks/verilog/divider/divider.ys -t divider -o model.smt2 -f benchmarks/verilog/divider/formula.hq -k 8 -s pes
```
which should return `result:unsat`


### Additional Installation for AutoHyper Comparison

Some helper scripts can compare against AutoHyper. To enable those options, install AutoHyper by following https://github.com/AutoHyper/AutoHyper and ensure its CLI binary is available on your `PATH`.





## HyperQB 2.0 CLI Usage


### Synopsis

```bash
cargo run --release -- (-n|-v) <models> -f <formula> -k <int> -s <sem> [options]
```

### Arguments

**Required**
- `-n <files>` | `-v <files>`: NuSMV or Verilog model files.
- `-f <file>`: Hyperproperty formula (`.hq`).
- `-t <name>`: Top module (Verilog only, defaults to `main`).
- `-k <int>` | `-l`: Unrolling bound in steps or enable loop conditions.
- `-s <pes|opt|hpes|hopt>`: Bounded semantics selection.

**Optional**
- `-m <int>`: Trajectory bound for AH-LTL fragments.
- `-c`: Emit counterexample when the formula is unsatisfied.
- `-q`: Use the QuAbS QBF solver instead of Z3.

### Example

Try the following example, which model check `linearizability (lin.hq)` on `SNARK algorithm (snark1_conc.smv, snark1_seq.smv)`:

```bash
cargo run --release -- -n benchmarks/2_snark/snark1_conc.smv benchmarks/2_snark/snark1_seq.smv -f benchmarks/2_snark/lin.hq -k 18 -s hpes -c
```

## Grammar of HyperLTL Specification


Formulas use the following grammar (identifiers: `pid` for paths, `tid` for trajectories):

```
path_formula ::= ("forall" | "exists") pid . form_rec
traj_formula ::= ("A" | "E") tid . AHLTL_rec
form_rec ::= path_formula | traj_formula | inner_HLTL
AHLTL_rec ::= traj_formula | inner_AHLTL
inner_HLTL ::= hform
inner_AHLTL ::= aform
hform ::= hform binary_op hform | unary_op hform | h_atom
aform ::= aform binary_op aform | unary_op aform | a_atom
h_atom ::= id[pid] | constant | number | "(" hform ")"
a_atom ::= id[pid][tid] | constant | number | "(" aform ")"
binary_op ::= "U" | "R" | "=" | "->" | "&" | "|"
unary_op ::= "G" | "F" | "X" | "~"
constant ::= "TRUE" | "FALSE"
number ::= [0-9]+ | "#b"(0|1)+
```

`inner_HLTL` covers standard HyperLTL fragments (only path quantifiers), while `inner_AHLTL` extends them with trajectory quantifiers. Use binary/unary temporal operators as usual; atoms reference propositions indexed by path and (optionally) trajectory identifiers.



## One-click shell scripts for running all benchmarks  


We provide one-click scripts to reproduce every table reported in our tool paper. 

### Reproducing Tables 4 & 5 (HLTL)

`run_hltl_1.sh` (Table 4) and `run_hltl_2.sh` (Table 5) run benchmark suites across multiple verification backends:

- **SMT** – Using Z3 as the SMT solver
- **AH** – Using AutoHyper
- **QBF** – Using QuAbs as the QBF solver

#### Usage

```bash
./run_hltl_1.sh [option]
./run_hltl_2.sh [option]
```

#### Main Options

| Option                         |                       Description                       |
| ------------------------------ | :-----------------------------------------------------: |
| `-list`                        |           List all available benchmark cases            |
| `-all <mode>`                  | Run all cases with the chosen mode (`smt`, `ah`, `qbf`) |
| `-light <mode>`                |      Run a lightweight subset (for quick testing)       |
| `-compare all [extras]`        |     Compare all case studies across the three modes     |
| `-compare light [extras]`      |    Compare lightweight cases across the three modes     |
| `-compare <case> [extras]`     |        Compare a specific case across all modes         |
| `-case <case> <mode> [extras]` |            Run one case under a single mode             |

#### Extra Option

| Option         | Description                                                  |
| -------------- | ------------------------------------------------------------ |
| `give_witness` | Extends SMT/AH runs with witness generation (when supported) |

To Reproduce **Tables 4 & 5 (HLTL)**, with SMT unrolling, run

```bash
./run_hltl_1.sh -all smt
./run_hltl_2.sh -all smt
```

### Reproducing Table 6 (AHLTL)

`run_ahltl.sh` runs benchmark suites using either **Z3** (SMT) or **QuAbs** (qbf) as the solver.

#### Usage

```bash
./run_ahltl.sh [option]
```

#### Options

| Option                              |                    Description                    |
| ----------------------------------- | :-----------------------------------------------: |
| `-list`                             |        List all available benchmark cases         |
| `-all <mode>`                       | Run all cases with the chosen mode (`smt`, `qbf`) |
| `-light <mode>`                     |   Run a lightweight subset (for quick testing)    |
| `-compare all`                      |     Compare all case studies across all modes     |
| `-compare <case_name>`              |     Compare a specific case across all modes      |
| `-case <case_name> <mode> [extras]` |  Run a case with one of the modes (`smt`, `qbf`)  |

To Reproduce **Table 6 (AHLTL)**, with SMT unrolling, run:

```bash
./run_ahltl.sh -all smt
```

### Reproducing Table 7 (Loop Condition)

`run_loopcond.sh` runs benchmark suites using the **Z3** (SMT) solver.

#### Usage

```bash
./run_loopcond.sh [option]
```

#### Options

| Option              |                  Description                  |
| ------------------- | :-------------------------------------------: |
| `-all`              |             Runs all case studies             |
| `-light`            | Runs a lightweight subset (for quick testing) |
| `-case <case_name>` |          Runs a specific case study           |
| `-list`             |       Lists all available case studies        |

To Reproduce **Table 7**, with SMT unrolling, run:

```bash
./run_loopcond.sh -all
```

### Reproducing Table 8 (Verilog)

`run_verilog.sh` runs benchmark suites for Verilog case studies using the **Z3** (SMT) solver.

#### Usage

```bash
./run_verilog.sh [option]
```

#### Options

| Option              |                  Description                  |
| ------------------- | :-------------------------------------------: |
| `-all`              |             Runs all case studies             |
| `-light`            | Runs a lightweight subset (for quick testing) |
| `-case <case_name>` |          Runs a specific case study           |
| `-list`             |       Lists all available case studies        |

To Reproduce **Table 8**, with SMT unrolling, run:

```bash
./run_verilog.sh -all
```



## Collecting Outputs

All outputs are printed to the screen during execution and simultaneously logged in the `_outfiles` directory.


