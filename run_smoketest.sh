#!/bin/bash

# Run the light cases on Table 4 (TACAS'21 paper) for the smoke test
# Expected to run ~90 seconds 
./run_hltl_1.sh -compare light


# Run the light cases on Table 5 (new HLTL cases) for the smoke test
# Expected to run ~70 seconds
./run_hltl_2.sh -compare light

# Run the light cases on Table 6 (AHLTL cases) for the smoke test
# Expected to run ~60 seconds
./run_ahltl.sh -compare light

# Run all cases on Table 7 (loop condition cases) for the smoke test
# Expected to run ~10 seconds
./run_loopcond.sh -all

# Run all cases on Table 8 (Verilog cases) for the smoke test
# Expected to run ~8 seconds
./run_verilog.sh -all