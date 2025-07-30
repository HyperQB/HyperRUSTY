#!/bin/bash

#cargo run --release -- -n mini.smv mini.smv -f mini.hq -k 3 -s pes 

# AutoHyper/app/AutoHyper --nusmv mini.smv auto_mini.hq

#=== BAKERY ===#

# echo "bakery 3"
# cargo run --release -- -n benchmarks/1_bakery/bakery.smv benchmarks/1_bakery/bakery.smv -f benchmarks/1_bakery/symmetry.hq -k 10 -s hpes

# echo "AutoHyper"
# time AutoHyper/app/AutoHyper --nusmv benchmarks/1_bakery/bakery.smv benchmarks/AH_formulas/1.1.hq




# echo "bakery 7"
# time cargo run --release -- -n benchmarks/1_bakery/bakery7.smv benchmarks/1_bakery/bakery7.smv -f benchmarks/1_bakery/symmetry7.hq -k 10 -s hpes

#cargo run --release -- -n benchmarks/1_bakery/bakery9.smv benchmarks/1_bakery/bakery9.smv -f benchmarks/1_bakery/symmetry9.hq -k 10 -s hpes

# cargo run --release -- -n benchmarks/1_bakery/bakery11.smv benchmarks/1_bakery/bakery11.smv -f benchmarks/1_bakery/symmetry11.hq -k 10 -s hpes


#=== Linearizability ===#

# Lazy-list
# time cargo run --release -- -n benchmarks/lazy_list/lazy_list_conc.smv benchmarks/lazy_list/lazy_list_seq.smv -f benchmarks/lazy_list/lazy_list.hq -k 13 -s hpes

# Emm ABA bug

time cargo run --release -- -n benchmarks/emm_aba/emm_aba_conc.smv benchmarks/emm_aba/emm_aba_seq.smv -f benchmarks/emm_aba/emm_aba.hq -k 6 -s hpes


#=== SNARK ===#

# echo "snark 1"
# time cargo run --release -- -n benchmarks/2_snark/snark1_conc.smv benchmarks/2_snark/snark1_seq.smv -f benchmarks/2_snark/lin.hq -k 18 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/2_snark/snark1_conc.smv benchmarks/2_snark/snark1_seq.smv benchmarks/AH_formulas/2.1.hq



# #=== Non-interference ===#

# echo "ni correct"
# time cargo run --release -- -n benchmarks/3_ni/NI_correct.smv benchmarks/3_ni/NI_correct.smv -f benchmarks/3_ni/NI_formula.hq -k 50 -s hopt


# time AutoHyper/app/AutoHyper --nusmv benchmarks/3_ni/NI_correct.smv benchmarks/AH_formulas/3.hq



# echo "ni incorrect"
# cargo run --release -- -n benchmarks/3_ni/NI_incorrect.smv benchmarks/3_ni/NI_incorrect.smv -f benchmarks/3_ni/NI_formula.hq -k 50 -s hopt

# time AutoHyper/app/AutoHyper --nusmv benchmarks/3_ni/NI_incorrect.smv benchmarks/AH_formulas/3.hq





# #=== Non-repudiation Protocol ===#

# echo "nrp correct"
# cargo run --release -- -n benchmarks/4_nrp/NRP_correct.smv benchmarks/4_nrp/NRP_correct.smv -f benchmarks/4_nrp/NRP_formula.hq -k 20 -s pes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/4_nrp/NRP_correct.smv benchmarks/AH_formulas/4.hq

# echo "nrp incorrect"
# cargo run --release -- -n benchmarks/4_nrp/NRP_incorrect.smv benchmarks/4_nrp/NRP_incorrect.smv -f benchmarks/4_nrp/NRP_formula.hq -k 15 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/4_nrp/NRP_incorrect.smv benchmarks/AH_formulas/4.hq




#=== Robustness Planning ===#
# time cargo run --release -- -n benchmarks/5_planning/robotic_robustness_100.smv benchmarks/5_planning/robotic_robustness_100.smv -f benchmarks/5_planning/robotic_robustness_formula.hq -k 20 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/5_planning/robotic_robustness_100.smv benchmarks/AH_formulas/5.1.hq


# time cargo run --release -- -n benchmarks/5_planning/robotic_robustness_400.smv benchmarks/5_planning/robotic_robustness_400.smv -f benchmarks/5_planning/robotic_robustness_formula.hq -k 40 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/5_planning/robotic_robustness_400.smv benchmarks/AH_formulas/5.1.hq


# time cargo run --release -- -n benchmarks/5_planning/robotic_robustness_1600.smv benchmarks/5_planning/robotic_robustness_1600.smv -f benchmarks/5_planning/robotic_robustness_formula.hq -k 40 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/5_planning/robotic_robustness_1600.smv benchmarks/AH_formulas/5.1.hq


# time cargo run --release -- -n benchmarks/5_planning/robotic_robustness_3600.smv benchmarks/5_planning/robotic_robustness_3600.smv -f benchmarks/5_planning/robotic_robustness_formula.hq -k 120 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/5_planning/robotic_robustness_3600.smv benchmarks/AH_formulas/5.1.hq








#=== Shortest Path Planning ===#
# time cargo run --release -- -n benchmarks/5_planning/robotic_sp_100.smv benchmarks/5_planning/robotic_sp_100.smv -f benchmarks/5_planning/robotic_sp_formula.hq -k 20 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/5_planning/robotic_sp_100.smv benchmarks/AH_formulas/5.2.hq

# time cargo run --release -- -n benchmarks/5_planning/robotic_sp_400.smv benchmarks/5_planning/robotic_sp_400.smv -f benchmarks/5_planning/robotic_sp_formula.hq -k 40 -s hpes





#=== Mutation Testing ===#
# echo "mutation"
# cargo run --release -- -n benchmarks/6_mutation/mutation_testing.smv benchmarks/6_mutation/mutation_testing.smv -f benchmarks/6_mutation/mutation_testing.hq -k 10 -s pes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/6_mutation/mutation_testing.smv benchmarks/AH_formulas/6.hq


#=== Co-termination ===#
# time cargo run --release -- -n benchmarks/7_coterm/coterm1.smv benchmarks/7_coterm/coterm1.smv -f benchmarks/7_coterm/coterm.hq -k 10 -s hpes



#=== Deniability ===#
# time cargo run --release -- -n benchmarks/8_deniability/electronic_wallet.smv benchmarks/8_deniability/electronic_wallet.smv benchmarks/8_deniability/electronic_wallet.smv -f benchmarks/8_deniability/den.hq -k 10 -s hpes



#=== Shared buffer ===#
# time cargo run --release -- -n benchmarks/9_buffer/scheduled_buffer.smv benchmarks/9_buffer/scheduled_buffer.smv -f benchmarks/9_buffer/classic_OD.hq -k 10 -s hpes

# time cargo run --release -- -n benchmarks/9_buffer/scheduled_buffer.smv benchmarks/9_buffer/scheduled_buffer.smv -f benchmarks/9_buffer/intrans_OD.hq -k 10 -s hpes

# time cargo run --release -- -n benchmarks/9_buffer/scheduled_buffer.smv benchmarks/9_buffer/scheduled_buffer.smv -f benchmarks/9_buffer/intrans_GMNI.hq -k 10 -s hpes

# time cargo run --release -- -n benchmarks/9_buffer/unscheduled_buffer.smv benchmarks/9_buffer/unscheduled_buffer.smv -f benchmarks/9_buffer/classic_OD.hq -k 10 -s hpes



#=== Non-determinism Experience ===#
# time cargo run --release -- -n benchmarks/10_NIexp/ni_example.smv benchmarks/10_NIexp/ni_example.smv -f benchmarks/10_NIexp/tini.hq -k 10 -s hpes


# time cargo run --release -- -n benchmarks/10_NIexp/ni_example.smv benchmarks/10_NIexp/ni_example.smv -f benchmarks/10_NIexp/tsni.hq -k 10 -s hpes


#=== k-safety ===#
# time cargo run --release -- -n benchmarks/11_ksafety/doubleSquare.smv benchmarks/11_ksafety/doubleSquare.smv -f benchmarks/11_ksafety/doubleSquare.hq -k 10 -s hpes



#=== Mapping synthesis ===#
# time cargo run --release -- -n benchmarks/12_mapsynth/msynth_MM.smv  benchmarks/12_mapsynth/msynth_MA.smv benchmarks/12_mapsynth/msynth_MB.smv benchmarks/12_mapsynth/msynth_MA.smv benchmarks/12_mapsynth/msynth_MB.smv -f benchmarks/12_mapsynth/msynth.hq -k 10 -s hpes


# time cargo run --release -- -n benchmarks/12_mapsynth/msynth2_MM.smv  benchmarks/12_mapsynth/msynth2_MA.smv benchmarks/12_mapsynth/msynth2_MB.smv benchmarks/12_mapsynth/msynth2_MA.smv benchmarks/12_mapsynth/msynth2_MB.smv -f benchmarks/12_mapsynth/msynth2.hq -k 10 -s hpes


#=== TEAM LTL ===#
# time cargo run --release -- -n benchmarks/13_teamltl/team.smv benchmarks/13_teamltl/team.smv benchmarks/13_teamltl/team.smv -f benchmarks/13_teamltl/team.hq -k 10 -s hpes

# time cargo run --release -- -n benchmarks/13_teamltl/team2.smv benchmarks/13_teamltl/team2.smv benchmarks/13_teamltl/team2.smv -f benchmarks/13_teamltl/team.hq -k 10 -s hpes



#=== NDET ===#
# time cargo run --release -- -n benchmarks/14_ndet/NI_v1.smv benchmarks/14_ndet/NI_v1.smv -f benchmarks/14_ndet/NI.hq -k 10 -s hpes

# time cargo run --release -- -n benchmarks/14_ndet/NI_v2.smv benchmarks/14_ndet/NI_v2.smv -f benchmarks/14_ndet/NI.hq -k 10 -s hpes

# time cargo run --release -- -n benchmarks/14_ndet/NI_v3.smv benchmarks/14_ndet/NI_v3.smv -f benchmarks/14_ndet/NI.hq -k 10 -s hpes





#=== LOOP CONDITIONS EXAMPLES ===#

# cargo run --release -- -n benchmarks/loop_conditions/abp/abp_1.smv benchmarks/loop_conditions/abp/abp_2.smv -f benchmarks/loop_conditions/abp/abp.hq -l

# cargo run --release -- -n benchmarks/loop_conditions/robust_path_planning/rp_1.smv benchmarks/loop_conditions/robust_path_planning/rp_2.smv -f benchmarks/loop_conditions/robust_path_planning/rp.hq -l

# cargo run --release -- -n benchmarks/loop_conditions/robust_path_planning/rp_1_no_sol.smv benchmarks/loop_conditions/robust_path_planning/rp_2.smv -f benchmarks/loop_conditions/robust_path_planning/rp.hq -l

# cargo run --release -- -n benchmarks/loop_conditions/simple_loop/simple_loop1.smv benchmarks/loop_conditions/simple_loop/simple_loop2.smv -f benchmarks/loop_conditions/simple_loop/simple_loop.hq -l

# cargo run --release -- -n benchmarks/loop_conditions/test_loop/rs1.smv benchmarks/loop_conditions/test_loop/rs2.smv -f benchmarks/loop_conditions/test_loop/rs.hq -l