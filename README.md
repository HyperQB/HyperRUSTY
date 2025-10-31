# HyperQB-2.0


## TACAS 2026 artifact evaluation requirements



### "A hyperlink to the artifact"

TBD!!!!!!

### "Additional requriements and installation" 
> "Additional requirements for the artifact, such as installation of proprietary software or particular hardware resources"

- Install [Docker](https://www.docker.com/) (instructions can be found [here](https://docs.docker.com/get-docker/)) (tested with version 25.0.3) and **start the Docker daemon**. 


TBD!!!!!!


### "Detailed instructions for smoke test"
> "Detailed instruction for an early smoke test review that allows reviewers to: (1) verify that the artifact can properly run; and (2) perform a short evaluation of the artifact before the full evaluation and detect any difficulties (see Rebuttal)"

We prepare several easy-to-use shell scripts for a smoke test. The purpose is to have the reviewers quickly test each script that aims at reproducing the empirical results in our paper. We write one script per table: 
1) `run_hltl_1.sh`      : Reproducing Table 4 "HyperLTL benchmarks from citation 22"

First, ensure that all light cases with SMT run smoothly:
```bash
./run_hltl_1.sh -light smt
```

Next, ensure that all light cases with QBF run smoothly: 
```bash
./run_hltl_1.sh -light qbf
```
If any error shows up for the above case, please check the previous section `setup.sh` again.


Finally, make sure AutoHyper (the baseline tool we compared with) executes smoothly:
```bash
./run_hltl_1.sh -light ah
```

If all of the above succeed, try to run the following command that runs all 3 modes:
```bash
./run_hltl_1.sh -compare light
```
And, make sure they can output witnesses:
```bash
./run_hltl_1.sh -compare light give_witness
```








1) `run_hltl_2.sh`      : Reproducing Table 5 "New HyperLTL benchmarks"
2) `run_ahltl.sh`       : Reproducing Table 5 "A-HLTL benchamrks from citation 20"
3) `run_loopcond.sh`    : Reproducing Table 7 "Loop condition benchmarks from citation 21"
4) `run_verilog`        : Reproducing Table 8 "Selected case studies in Verilog" 





### "Detailed instructions for replication of results in the paper"
> "Detailed instructions for use of the artifact and replication of results in the paper, including estimated resource use and required time if non-trivial"



### "List of badges we are applying"
> "List of badges you are applying for in your submission. In particular, if you are not applying for the Reusable badge, please indicate it?\"




### "Platform tested"
> "Platforms you tested this on (in particular: the host architecture: arm64 vs amd64, the operating system, etc.)"

[] TACAS VM for x86_64
[] TACAS VM for arm64
[] Docker on x86_64
[] Docker on arm64
[] Windows host system
[] Linux host system
[] macOS host system



### Additions notes by the HyperQB-2.0 team



#### Verilog 

While preparing the artifact on certain Verilog case studies we discovered that using the `-c` option even on sat results results in much better solver performance for Z3.
