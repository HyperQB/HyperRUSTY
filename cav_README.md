# HyperQB 2.0

**Artifact ID:** `210`  
**Paper Title:** `HyperQB 2.0: A Bounded Model Checker for Hyperproperties`
**Zenodo DOI:** -
**Zenodo Record:** -

This artifact provides a **Docker image** (distributed via **Docker Hub** and **Zenodo**) that contains the complete experimental environment along with the **shell scripts** required to reproduce all tables reported in the paper. To regenerate the results, the AEC only needs to: (1) install Docker, (2) pull our image from Docker Hub, (3) start the container, and (4) run the provided scripts inside it.

**For consistency with the Docker environment, we recommend using the Docker Hub image described in [Option 1](#option1) as the primary method.**

Instructions for obtaining the artifact via Zenodo are provided in [Option 2](#option2).

**Expected outputs:** Printed in Console and logged in `_outfiles` directory.

---

### Remarks on Dependencies of the Docker Artifact

1. **SPOT errors from AutoHyper:**
   Our artifact includes comparisons with the external model checker `AutoHyper`, which depends on `SPOT`. During testing of the image, we found that SPOT occasionally produces errors on certain inputs. These issues originate within SPOT and are outside the scope of our tool. Unfortunately, we do not have sufficient insight into `SPOT`’s internals to debug these errors reliably.

2. **Out-of-memory from QuAbS:**
   Depending on the hardware and Docker resource limits on the reviewer’s machine, some large instances may also encounter _out-of-memory_ termination (i.e., _command terminated by signal 9_ messages in the terminal), and we flag those cases as `MEMOUT` when displaying the results. Such behavior is due to performance and resource limitations of the underlying solvers (e.g., `QuAbS`) when run inside Docker, and should not be interpreted as a limitation of the HyperQB 2.0 tool itself.

Our primary goal in this artifact submission is to provide a _fully reproducible Docker image_ that allows reviewers to run the complete set of experiments described in the paper.
---

## Hyperlink to the artifact:

-

---

## Badges we are applying for:

We aim to apply for all 3 badges, following the TACAS 2026 artifact submission guidelines, including:

1. **Available**: HyperQB 2.0 source code and its dependencies are publicly available on Zenodo with a permanent DOI (as a Docker image).
2. **Functional**: Our artifact can easily reproduce all key results from the submitted paper (see detailed instructions below).
3. **Reusable**: HyperQB 2.0 comes with a complete user manual (HyperQB_Manual.pdf) included in the artifact submission. Pages 7–8 provide detailed documentation of the command-line interface that can be easily adapted for future research.

HyperQB 2.0 official website: https://hyperqb.github.io/index.html

## Table of Contents

1. [System Requirements](#sysreq)
1. [What You Will Download](#download)
1. [Install Docker](#docker)
1. [Obtaining the Artifact](#artifact)
1. [Reproduce Experiments](#experiments)
1. [Collecting Outputs](#outputs)
1. [Reusability](#reuse)
1. [Notices](#notices)

---

## <a name="sysreq"></a> System Requirements

- **Operating Systems:**
  - macOS 12+ (Apple Silicon)
- **CPU:** 2+ cores recommended
- **RAM:** ≥ 8 GB recommended (≥ 16 GB ideal for the largest experiments)
- **Disk:** ≥ 20 GB free space
- **Internet:** required once to pull the artifact from Docker Hub
- **GPU:** _not required_ (all experiments run on CPU)

---

## <a name="download"></a> What You Will Download

We present our artifact as a Docker image.
Inside the image, you will find:

- All dependencies and toolchains
- Ready-to-run shell scripts:
  - `run_hltl_1.sh` – Reproducing Table 4
  - `run_hltl_2.sh` – Reproducing Table 5 HLTL benchmarks
  - `run_ahltl.sh` – Reproducing Table 6 A-HLTL benchmarks
  - `run_loopcond.sh` – Reproducing Table 7
  - `run_verilog.sh` – Reproducing Table 8

---

## <a name="docker"></a> Install Docker

### macOS (Apple Silicon)

1. Install **Docker Desktop for Mac**.
2. After installation, launch Docker Desktop and wait until it says **“Docker is running.”**

### Verify Docker Works

Open a terminal and run:

```bash
docker --version
docker run --rm hello-world
```

You should see **“Hello from Docker!”** If this works, Docker is correctly installed.

---

## <a name="artifact"></a> Obtaining the Artifact

The artifact is provided as a public Docker image available on Docker Hub and Zenodo. Instructions for both download methods are provided below.

### <a name="option1"></a> Option 1: Docker Hub (preffered)

Please ensure you have an active internet connection and Docker is running.


#### macOS

For arm64 use `rogaleke/hyperqb2.0:arm64`.

### Running the container

Because the artifact runs inside a Docker container, any generated outputs and logs remain inside the container’s filesystem and are lost when the container exits. To preserve these files, you should mount a directory from your host machine into the container so that all generated outputs are written directly to your local filesystem.

To begin, navigate to the directory from which you want to run the Docker image. Then create a new directory named `_outfiles` to store all output produced by HyperQB 2.0. You can create it with the following command:

#### macOS (Terminal)

```bash
# Create a directory to store outputs
mkdir -p _outfiles

# run the image
docker run --rm -it \
  -v "$(pwd)/_outfiles:/build/HyperRUSTY/_outfiles" \
  rogaleke/hyperqb2.0:arm64 \
  bash
```

### <a name="option2"></a> Option 2: Zenodo

**Notice**: This image is only for **ARM64** architecture.

From our [Zenodo record](https://zenodo.org/records/17654609), download the `.tar` containing the Docker image. Then, navigate to the directory where it was downloaded and run:

```bash
docker load -i hyperqb2.tar
```

next, check if the image is loaded by running:

```bash
docker images
```

If the image is loaded correctly, you should be able to see the `rogaleke/hyperqb2.0` entry:

```
REPOSITORY             TAG       IMAGE ID       CREATED             SIZE
rogaleke/hyperqb2.0    arm64     1a170594cf8b   24 hours ago        10.4GB
```

(`CREATED` could vary depending on when you pull the image)

Finally, to run this image, follow the instructions below.

Because the artifact runs inside a Docker container, any generated outputs and logs remain inside the container’s filesystem and are lost when the container exits. To preserve these files, you should mount a directory from your host machine into the container so that all generated outputs are written directly to your local filesystem.

To begin, navigate to the directory from which you want to run the Docker image. Then create a new directory named `_outfiles` to store all output produced by HyperQB 2.0. You can create it with the following command:

#### macOS (Terminal)

```bash
# Create a directory to store outputs
mkdir -p _outfiles

# run the image
docker run --rm -it \
  -v "$(pwd)/_outfiles:/build/HyperRUSTY/_outfiles" \
  rogaleke/hyperqb2.0:arm64 \
  bash
```

You are now inside the HyperQB2.0 Docker image.

---

## <a name="experiments"></a> Reproduce Experiments

We now describe in detail how to reproduce the complete results presented in the paper. To ensure correct execution, please adjust the `TIMEOUT` parameter defined at the top (line 5) of each shell script according to your machine’s setup. Currently, the default value is **60 seconds**. We leave this value for reviewers to determine based on their computing environment.

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
| `-heavy <mode>`                |         Run a heavy subset (for deeper testing)         |
| `-compare all [extras]`        |     Compare all case studies across the three modes     |
| `-compare light [extras]`      |    Compare lightweight cases across the three modes     |
| `-compare heavy [extras]`      |       Compare heavy cases across the three modes        |
| `-compare <case> [extras]`     |        Compare a specific case across all modes         |
| `-case <case> <mode> [extras]` |            Run one case under a single mode             |

#### Extra Option

| Option         | Description                                                  |
| -------------- | ------------------------------------------------------------ |
| `give_witness` | Extends SMT/AH runs with witness generation (when supported) |

To Reproduce **Tables 4 & 5 (HLTL)**, after adjusting `TIMEOUT` (specified at the top of each shell script) to a large enough number, run:

```bash
./run_hltl_1.sh -compare all
./run_hltl_2.sh -compare all
```

### Reproducing Table 6 (AHLTL)

`run_ahltl.sh` runs benchmark suites using either **Z3** (SMT) or **QuAbS** (qbf) as the solver.

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
| `-heavy <mode>`                     |      Run a heavy subset (for deeper testing)      |
| `-compare all`                      |     Compare all case studies across all modes     |
| `-compare light`                    |    Compare lightweight cases across all modes     |
| `-compare heavy`                    |       Compare heavy cases across all modes        |
| `-compare <case_name>`              |     Compare a specific case across all modes      |
| `-case <case_name> <mode>         ` |  Run a case with one of the modes (`smt`, `qbf`)  |

To Reproduce **Table 6 (AHLTL)**, after adjusting `TIMEOUT` (specified at the top of each shell script) to a large enough number, run:

```bash
./run_ahltl.sh -compare all
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

To Reproduce **Table 7**, Run:

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

To Reproduce **Table 8**, Run:

```bash
./run_verilog.sh -all
```

---

## <a name="outputs"></a> Collecting Outputs

All outputs are printed to the screen during execution and simultaneously logged in the `_outfiles` directory.

---

## <a name="reuse"></a> Reusability

To check if HyperQB 2.0 compiled without error, execute:

```bash
cargo build --release
```

The compiled binary can be found in `target/release/`.

To test if HyperQB (SMT unrolling) can successfully compiled

```bash
cargo run --release -- -n benchmarks/sync/1_bakery/bakery3.smv benchmarks/sync/1_bakery/bakery3.smv -f benchmarks/sync/1_bakery/symmetry3.hq -k 10 -s hpes
```

which should return `result: unsat`

To test if HyperQB (QBF unrolling with `QuAbS`) can successfully run:

```bash
cargo run --release -- -n benchmarks/sync/1_bakery/bakery3.smv benchmarks/sync/1_bakery/bakery3.smv -f benchmarks/sync/1_bakery/symmetry3.hq -k 10 -s hpes
```

which should return `UNSAT`

To test if HyoerQB (with verilog input using `yosys`) can successfully run:

```bash
cargo run --release -- -v benchmarks/verilog/divider/divider.ys benchmarks/verilog/divider/divider.ys -t divider -o model.smt2 -f benchmarks/verilog/divider/formula.hq -k 8 -s pes
```

which should return `result:unsat`

### HyperQB 2.0 CLI Usage

We here provide detailed instruction to reuse HyperQB2.0

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

### CLI Example

Try the following example, which model check `linearizability (lin.hq)` on `SNARK algorithm (snark1_conc.smv, snark1_seq.smv)`:

```bash
cargo run --release -- -n benchmarks/sync/2_snark/snark1_conc.smv benchmarks/sync/2_snark/snark1_seq.smv -f benchmarks/sync/2_snark/lin.hq -k 18 -s hpes -c
```

which should return `UNSAT` with `counterexample` displayed in your terminal.

---

We would like to remark that, outside of this artifact, we offer a fully standalone **macOS application** (available for download from GitHub) with an **interactive GUI** (demonstrated on page 5 of the manual). Comprehensive information about the tool’s theoretical background, algorithms, case studies (including model descriptions), and an online version of the GUI is also accessible through our **official website**. Since these components are beyond the TACAS artifact evaluation scope, we provide here only the CLI binary for reviewers to interact with directly. However, HyperQB 2.0 is easy to adapt for future research to benefit the formal methods community.

---

We sincerely thank the Artifact Evaluation Committee for their time and feedback.
