# HyperQB 2.0

**Artifact ID:** `97`  
**Paper Title:** `HyperQB 2.0: A Bounded Model Checker for Hyperproperties` (tool paper submission 0087)   
**Zenodo DOI:** `10.5281/zenodo.17490665`  
**Zenodo Record:** `https://zenodo.org/records/17490665`

This artifact provides a **Docker image** (distributed via **Docker Hub**) that contains our full experimental environment and the **shell scripts** needed to reproduce the tables reported in the paper. The AEC only needs to (1) install Docker, (2) pull our image from Docker Hub, (3) load it into Docker, and (4) run the provided scripts inside the container to regenerate the results.

**Our artifact is available on both Zenodo and Docker Hub. For simplicity, the instructions below use the Docker Hub version as [OPTION1] (and the Zenodo version as [OPTION2]).**

**Expected outputs:** Printed in Console and logged in `_outfiles` directory.

---
## Hyperlink to the artifact: 

https://zenodo.org/records/17490665

---
## Badges we are applying for:

We aim to apply for all 3 badges, following the TACAS 2026 artifact submission guidelines, including: 
1) **Available**:   HyperQB 2.0 source code and its dependencies are publicly available on Zenodo with a permanent DOI (as a Docker image).
2) **Functional**:  Our artifact can easily reproduce all key results from the submitted paper (see detailed instructions below).
3) **Reusable**:    HyperQB 2.0 comes with a complete user manual (HyperQB_Manual.pdf) included in the artifact submission. Pages 7–8 provide detailed documentation of the command-line interface that can be easily adapted for future research. 

HyperQB 2.0 official website: https://hyperqb.github.io/index.html

We would like to remark that, outside of this artifact, we offer a fully standalone **macOS application** (available for download from GitHub) with an **interactive GUI** (demonstrated on page 5 of the manual). Comprehensive information about the tool’s theoretical background, algorithms, case studies (including model descriptions), and an online version of the GUI is also accessible through our **official website**. Since these components are beyond the TACAS artifact evaluation scope, we provide here only the CLI binary for reviewers to interact with directly. However, HyperQB 2.0 is easy to adapt for future research to benefit the formal methods community.

---
 

## Table of Contents

1. [System Requirements](#system-requirements)
2. [What You Will Download](#what-you-will-download)
3. [Install Docker](#install-docker)
4. [Verify Docker Works](#verify-docker-works)
5. [Obtain the Artifact Image from Docker Hub](#obtain-the-artifact-image-from-docker-hub)
6. [Create Host Folders for Results](#create-host-folders-for-results)
7. [Run the Container (Interactive Shell)](#run-the-container-interactive-shell)
8. [Inside the Container: Reproduce Experiments](#inside-the-container-reproduce-experiments)
9. [Collecting Outputs](#collecting-outputs)
10. [Notices](#notices)

---

## System Requirements

- **Operating Systems:**
  - macOS 12+ (Intel **or** Apple Silicon)
  - Windows 10/11 (Docker Desktop)
  - Linux (Ubuntu 20.04+, Debian, Fedora, etc.)
- **CPU:** 2+ cores recommended
- **RAM:** ≥ 8 GB recommended (≥ 16 GB ideal for the largest experiments)
- **Disk:** ≥ 20 GB free space
- **Internet:** required once to pull the artifact from Docker Hub
- **GPU:** _not required_ (all experiments run on CPU)

---

## What You Will Download

We present our artifact as a Docker image.
Inside the image, you will find:

- All dependencies and toolchains
- Ready-to-run shell scripts:
  - `run_hltl_1.sh` – Reproducing Table 4
  - `run_hltl_2.sh` – Reproducing Table 5 HLTL benchmarks
  - `run_ahltl.sh` – Reproducing Table 5 A-HLTL benchmarks
  - `run_loopcond.sh` – Reproducing Table 7
  - `run_verilog.sh` – Reproducing Table 8

---

## Install Docker

Choose **one** of the following:

### macOS (Intel or Apple Silicon)

1. Install **Docker Desktop for Mac**.
2. After installation, launch Docker Desktop and wait until it says **“Docker is running.”**

### Windows 10/11

1. Install **Docker Desktop for Windows**.
2. Ensure **Virtualization** is enabled in BIOS if prompted.
3. Launch Docker Desktop and wait until it says **“Docker is running.”**

> On Windows, we recommend using **PowerShell** for the commands below.

### Linux (Ubuntu/Debian/Fedora/etc.)

Install the Docker Engine from your distribution or Docker’s official repository. For Ubuntu/Debian:

```bash
# Run as a regular user with sudo privileges
sudo apt-get update
sudo apt-get install -y ca-certificates curl gnupg
sudo install -m 0755 -d /etc/apt/keyrings
curl -fsSL https://download.docker.com/linux/ubuntu/gpg   | sudo gpg --dearmor -o /etc/apt/keyrings/docker.gpg
echo   "deb [arch=$(dpkg --print-architecture) signed-by=/etc/apt/keyrings/docker.gpg]   https://download.docker.com/linux/ubuntu $(. /etc/os-release; echo $VERSION_CODENAME) stable"   | sudo tee /etc/apt/sources.list.d/docker.list > /dev/null
sudo apt-get update
sudo apt-get install -y docker-ce docker-ce-cli containerd.io
```

_(Fedora / Arch / others: use your package manager or Docker’s instructions.)_

---

## Verify Docker Works

Open a terminal (macOS/Linux) or PowerShell (Windows) and run:

```bash
docker --version
docker run --rm hello-world
```

You should see **“Hello from Docker!”** If this works, Docker is correctly installed.

---

### <mark>(!!!) Important note on internet access during artifact setup</mark>

We are fully aware of the internet access restrictions during the TACAS artifact evaluation. Therefore, we provide two alternative options:

**[OPTION 1]**: Pull the HyperQB image from Docker Hub

**[OPTION 2]**: Download the HyperQB image from Zenodo

We recommend using [OPTION 1]. However, if pulling directly from Docker Hub is not possible, the image is also available for download from our permanent online repository on Zenodo. This serves as a flexible alternative in case one of the options does not work on the reviewer’s machine.

---

## [OPTION 1]: Obtain the Artifact Image from Docker Hub

The artifact is distributed as a public Docker image hosted on Docker Hub.

Please ensure you have an active internet connection and Docker is running.

### macOS / Linux (Terminal)

```bash
# Create a working directory
mkdir -p ~/tacas-ae && cd ~/tacas-ae

# Pull the latest image from Docker Hub
docker pull rogaleke/hyperqb2.0:latest

```

### Windows (PowerShell)

```powershell
# Create a working directory (optional)
New-Item -ItemType Directory -Force -Path "$HOME\tacas-ae" | Out-Null
Set-Location "$HOME\tacas-ae"

# Pull the latest image from Docker Hub
docker pull rogaleke/hyperqb2.0:latest
```

> **File size note:** The tarball can be several GB. Ensure sufficient disk space and a stable network connection.

---

## Run the Container (Interactive Shell)

Start the container with sensible defaults. **Copy exactly one** of the following run commands.

Troubleshoot: if any of the following commands failed with `Unable to find image...`, make sure to run `docker images` to check what exactly the name of the repository you pulled. 

### macOS/Linux (bash/zsh)

```bash
# Basic run
docker run --rm -it rogaleke/hyperqb2.0:latest
```

### Windows (PowerShell)

```powershell
docker run --rm -it rogaleke/hyperqb2.0:latest
```

> **What this does:**
>
> - `--rm` cleans up when you exit.
> - `-it` gives you an interactive shell.

You should now see a shell prompt **inside** the container, typically like: `root@<container-id>:/workspace#`

You are now in a ready-to-go environment to run HyperQB! Yay!

---

## [OPTION2] Download docker image from Zenodo 

From our Zenodo link (https://zenodo.org/records/17490665), download the `.tar` that contains the docker image, then run:
```bash
docker load -i hyperqb2.tar
```
next, check if the image is loaded by running:
```bash
docker images
```
if the image is loaded correctly, you should be able to see the `hyperqb-docker` entry:
```
REPOSITORY            TAG       IMAGE ID       CREATED             SIZE
hyperqb-docker        latest    41ea36748c37   18 minutes ago      7.87GB
``` 
finally, run this image:
```bash
docker run -it hyperqb-docker:latest
```
You are now in a ready-to-go environment to run HyperQB! Yay!


---

## Inside the Container, stage 1: Smoke Test

We provide easy-to-use shell scripts tailored for the early light review. To facilitate quick testing, we set a small `TIMEOUT` value in these scripts, allowing reviewers to run through all cases efficiently.

To ensure that all tables are reproducible and ready for further evaluation, please execute the following command:
- `./run_hltl_1.sh -compare all`
- `./run_hltl_2.sh -compare all`
- `./run_ahltl -all`
- `./run_loopcond.sh -all`
- `./run_verilog -all`

If no errors are reported, the smoke test is successful!

---

## Inside the Container, stage 2: Reproduce Experiments

We now describe in detail how to reproduce the complete results presented in the paper. To ensure correct execution, <mark>please adjust the `TIMEOUT` parameter defined at the top (line 5) of each shell script according to your machine’s setup.<mark/> We leave this value for reviewers to determine based on their computing environment.


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

To Reproduce **Tables 4 & 5 (HLTL)**, after adjusting `TIMEOUT` to a large enough number, run:

```bash
./run_hltl_1.sh -compare all
./run_hltl_2.sh -compare all
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

To Reproduce **Table 6 (AHLTL)**, Run:

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

## Collecting Outputs

All outputs are printed to the screen during execution and simultaneously logged in the `_outfiles` directory.

---

## Notices

### Notice 1: During the preparation of the artifact, we discovered that the first two cases in the Loop Peeling benchmarks (`LP` and `LP_ndet`) contained a minor bug in the model. After correcting it, the QBF timings differed from those originally reported in the paper. Furthermore, the first ELFP entry is UNSAT; the checkmark shown in the paper is a typo.

### Notice 2: While preparing the artifact for the Verilog case studies, we discovered that using the `-c` option, even on satisfiable (SAT) results, significantly improves Z3's solver performance.

We sincerely thank the Artifact Evaluation Committee for their time and feedback.
