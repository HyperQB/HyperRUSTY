# HyperQB 2.0

**Artifact ID:** `97`  
**Paper Title:** `HyperQB 2.0: A Bounded Model Checker for
Hyperproperties`

This artifact provides a **Docker image** (distributed via **Docker Hub**) that contains our full experimental environment and the **shell scripts** needed to reproduce the tables reported in the paper. The AEC only needs to (1) install Docker, (2) pull our image from Docker Hub, (3) load it into Docker, and (4) run the provided scripts inside the container to regenerate the results.

- <mark>**Expected outputs:** CSV/Markdown/LaTeX tables in `./results/tables/` on the host</mark>

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

> <mark>**x86_64 / amd64 hosts (Intel/AMD PCs, Intel Macs):** If the image is published for `linux/amd64`, it runs **natively**—no flags required. If the image is **`linux/arm64`‑only**, either use our multi‑arch/amd64 build **or** run under emulation with `--platform=linux/arm64`. Docker Desktop includes QEMU emulation by default; on native Linux you may need `binfmt`/`qemu-user-static`. Emulation works but is slower.</mark>

---

## What You Will Download

From Docker Hub, pull the artifact's Docker image.

Inside the image, you will find:

- All dependencies and toolchains
- Scripts:
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

## Obtain the Artifact Image from Docker Hub

The artifact is distributed as a public Docker image hosted on Docker Hub.

Please ensure you have an active internet connection and Docker is running.

### macOS / Linux (Terminal)

```bash
# Create a working directory
mkdir -p ~/tacas-ae && cd ~/tacas-ae

# Pull the latest image from Docker Hub
docker pull yourorg/hyperqb2.0:latest

```

### Windows (PowerShell)

```powershell
# Create a working directory (optional)
New-Item -ItemType Directory -Force -Path "$HOME\tacas-ae" | Out-Null
Set-Location "$HOME\tacas-ae"

# Pull the latest image from Docker Hub
docker pull yourorg/hyperqb-docker:latest
```

> **File size note:** The tarball can be several GB. Ensure sufficient disk space and a stable network connection.

---

## Run the Container (Interactive Shell)

Start the container with sensible defaults. **Copy exactly one** of the following run commands.

### macOS/Linux (bash/zsh)

```bash
# Basic run
docker run --rm -it hyperqb-docker:latest
```

### Windows (PowerShell)

```powershell
# Ensure you run this from the folder that contains .\data and .\results
docker run --rm -it `
  --name ae-container `
  -v "${PWD}\data:/data" `
  -v "${PWD}\results:/results" `
  REPO/IMAGE:TAG `
  /bin/bash
```

> **What this does:**
>
> - `--rm` cleans up when you exit.
> - `-it` gives you an interactive shell.
> - `-v host:container` mounts folders so outputs persist on your machine.
> - `/bin/bash` drops you inside the container.

You should now see a shell prompt **inside** the container, typically like:  
`root@<container-id>:/workspace#`

---

## Inside the Container: Reproduce Experiments

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

To Reproduce **Tables 4 & 5 (HLTL)**, Run:

```bash
./run_hltl_1.sh -compare all
./run_hltl_2.sh -compare all
```

### Reproducing Table 5 (AHLTL)

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

To Reproduce **Table 5 (AHLTL)**, Run:

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

### Notice 1: During the preparation of the artifact, we discovered that the first two cases in the Loop Peeling benchmarks (`LP` and `LP_ndet`) contained a minor bug in the model. After correcting it, the QBF timings differed from those originally reported in the paper.

### Notice 2: While preparing the artifact for the Verilog case studies, we discovered that using the `-c` option, even on satisfiable (SAT) results, significantly improves Z3's solver performance.

We thank the Artifact Evaluation Committee for their time and feedback.
