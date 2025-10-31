# HyperQB 2.0

**Artifact ID:** `97`  
**Paper Title:** `HyperQB 2.0: A Bounded Model Checker for
Hyperproperties`  
**Zenodo DOI:** `10.5281/zenodo.<DOI_SUFFIX>`  
**Zenodo Record:** `https://zenodo.org/records/<RECORD_ID>`

This artifact provides a **Docker image** (distributed via **Zenodo**) that contains our full experimental environment and the **shell scripts** needed to reproduce the tables reported in the paper. The AEC only needs to (1) install Docker, (2) download our image from Zenodo, (3) load it into Docker, and (4) run the provided scripts inside the container to regenerate the results.

- <mark>**Expected outputs:** CSV/Markdown/LaTeX tables in `./results/tables/` on the host</mark>

---

## Table of Contents

1. [System Requirements](#system-requirements)
2. [What You Will Download](#what-you-will-download)
3. [Install Docker](#install-docker)
4. [Verify Docker Works](#verify-docker-works)
5. [Obtain the Artifact Image from Zenodo](#obtain-the-artifact-image-from-zenodo)
6. [Load and Tag the Image](#load-and-tag-the-image)
7. [Create Host Folders for Results](#create-host-folders-for-results)
8. [Run the Container (Interactive Shell)](#run-the-container-interactive-shell)
9. [Inside the Container: Reproduce Experiments](#inside-the-container-reproduce-experiments)
10. [Collecting Outputs](#collecting-outputs)
11. [One-Command Convenience (Optional)](#one-command-convenience-optional)
12. [Troubleshooting](#troubleshooting)
13. [FAQ](#faq)
14. [Citation & Acknowledgments](#citation--acknowledgments)
15. [Final Checklist (for the AEC)](#final-checklist-for-the-aec)
16. [Placeholders to Replace Before Release](#placeholders-to-replace-before-release)

---

## System Requirements

- **Operating Systems:**
  - macOS 12+ (Intel **or** Apple Silicon)
  - Windows 10/11 (Docker Desktop)
  - Linux (Ubuntu 20.04+, Debian, Fedora, etc.)
- **CPU:** 2+ cores recommended
- **RAM:** ≥ 8 GB recommended (≥ 16 GB ideal for the largest experiments)
- **Disk:** ≥ 20 GB free space
- **Internet:** required once to download the Zenodo artifact
- **GPU:** _not required_ (all experiments run on CPU)

> <mark>**x86_64 / amd64 hosts (Intel/AMD PCs, Intel Macs):** If the image is published for `linux/amd64`, it runs **natively**—no flags required. If the image is **`linux/arm64`‑only**, either use our multi‑arch/amd64 build **or** run under emulation with `--platform=linux/arm64`. Docker Desktop includes QEMU emulation by default; on native Linux you may need `binfmt`/`qemu-user-static`. Emulation works but is slower.</mark>

---

## What You Will Download

From the Zenodo record <mark>`https://zenodo.org/records/<RECORD_ID>`</mark>, download the Docker image tarball suitable for your system's architecture:

`<artifact-image-amd64.tar.gz>` _(or)_ `<artifact-image-arm64.tar.gz>`

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

## Obtain the Artifact Image from Zenodo

### macOS / Linux (Terminal)

```bash
# Create a working directory
mkdir -p ~/tacas-ae && cd ~/tacas-ae

# Download the tarball (replace file name and URL as shown on Zenodo)
curl -L -o artifact-image.tar.gz "https://zenodo.org/records/<RECORD_ID>/files/<artifact-image-amd64.tar.gz>?download=1"

```

### Windows (PowerShell)

```powershell
# Create a working directory
New-Item -ItemType Directory -Force -Path "$HOME\tacas-ae" | Out-Null
Set-Location "$HOME\tacas-ae"

# Download (replace with your Zenodo file URL)
Invoke-WebRequest -Uri "https://zenodo.org/records/<RECORD_ID>/files/<artifact-image-amd64.tar.gz>?download=1" -OutFile "artifact-image.tar.gz"

```

> **File size note:** The tarball can be several GB. Ensure sufficient disk space and a stable network connection.

---

## Load and Tag the Image

After downloading, load the image into Docker:

```bash
docker load -i artifact-image.tar.gz
```

You should see output similar to:

```
Loaded image: REPO/IMAGE:TAG
```

If the output does **not** display a name/tag, list images and **tag** it manually:

```bash
docker images --digests
# Suppose IMAGE ID is abcdef123456
docker tag abcdef123456 REPO/IMAGE:TAG
```

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

All paths below are **inside** the container.

1. **Sanity check the environment** (optional but recommended):

   ```bash
   ./scripts/bootstrap.sh
   ```

   This verifies tools, versions, and writable paths (`/results`, `/data`). Any missing optional assets will be fetched or you’ll be prompted with instructions.

2. **Run all experiments**:

   ```bash
   ./scripts/run_all_experiments.sh
   ```

   - This script runs the complete experimental suite used in the paper.
   - Progress and logs are written to `/results/logs/` and `/results/run.json`.
   - If your time is limited, see **FAQ: Running a smaller subset**.

3. **Generate final tables** (CSV/Markdown/LaTeX):

   ```bash
   ./scripts/generate_tables.sh
   ```

   - Outputs are written to `/results/tables/`.
   - Files are named to match the paper (e.g., `table1_summary.csv`, `table2_ablation.md`, `table3_main.tex`).

> **Determinism:** We fix random seeds internally where applicable. If nondeterminism is unavoidable (e.g., external solvers), the scripts aggregate multiple runs and report medians/means with confidence intervals.

---

## Collecting Outputs

Exit the container (`exit` or `Ctrl-D`). Your results are now available **on the host**:

```
./results/
  logs/
  run.json
  tables/
    table1_summary.csv
    table2_ablation.md
    table3_main.tex
```

These files are safe to attach or compare with the paper’s reported tables.

---

We thank the Artifact Evaluation Committee for their time and feedback.
