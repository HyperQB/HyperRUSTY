# !/bin/bash

#cargo run --release -- -n mini.smv mini.smv -f mini.hq -k 3 -s pes 

# AutoHyper/app/AutoHyper --nusmv mini.smv auto_mini.hq

#=== BAKERY ===#

# echo "bakery 3"
# cargo run --release -- -n benchmarks/sync/1_bakery/bakery.smv benchmarks/sync/1_bakery/bakery.smv -f benchmarks/sync/1_bakery/symmetry.hq -k 10 -s hpes

# echo "AutoHyper"
# time AutoHyper/app/AutoHyper --nusmv benchmarks/1_bakery/bakery.smv benchmarks/AH_formulas/1.1.hq




# echo "bakery 7"
# time cargo run --release -- -n benchmarks/1_bakery/bakery7.smv benchmarks/1_bakery/bakery7.smv -f benchmarks/1_bakery/symmetry7.hq -k 10 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/1_bakery/bakery7.smv benchmarks/AH_formulas/1.7.hq --log --witness

# cargo run --release -- -n benchmarks/1_bakery/bakery9.smv benchmarks/1_bakery/bakery9.smv -f benchmarks/1_bakery/symmetry9.hq -k 10 -s hpes -q

# time AutoHyper/app/AutoHyper --nusmv benchmarks/1_bakery/bakery9.smv benchmarks/AH_formulas/1.9.hq --log --witness

# time AutoHyper/app/AutoHyper --nusmv benchmarks/1_bakery/bakery7.smv benchmarks/AH_formulas/1.7.hq --log --witness

# cargo run --release -- -n benchmarks/1_bakery/bakery9.smv benchmarks/1_bakery/bakery9.smv -f benchmarks/1_bakery/symmetry9.hq -k 10 -s hpes -q

# time AutoHyper/app/AutoHyper --nusmv benchmarks/1_bakery/bakery9.smv benchmarks/AH_formulas/1.9.hq --log --witness

# cargo run --release -- -n benchmarks/1_bakery/bakery11.smv benchmarks/1_bakery/bakery11.smv -f benchmarks/1_bakery/symmetry11.hq -k 10 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/1_bakery/bakery11.smv benchmarks/AH_formulas/1.11.hq --log --witness


#=== Linearizability ===#

# Lazy-list
# time cargo run --release -- -n benchmarks/lazy_list/lazy_list_conc.smv benchmarks/lazy_list/lazy_list_seq.smv -f benchmarks/lazy_list/lazy_list.hq -k 13 -s hpes

# Emm ABA bug

# time cargo run --release -- -n benchmarks/emm_aba/emm_aba_conc.smv benchmarks/emm_aba/emm_aba_seq.smv -f benchmarks/emm_aba/emm_aba.hq -k 6 -s hpes

#=== Linearizability ===#

# Lazy-list
# time cargo run --release -- -n benchmarks/lazy_list/lazy_list_conc.smv benchmarks/lazy_list/lazy_list_seq.smv -f benchmarks/lazy_list/lazy_list.hq -k 13 -s hpes

# Emm ABA bug

#time cargo run --release -- -n benchmarks/emm_aba/emm_aba_conc.smv benchmarks/emm_aba/emm_aba_seq.smv -f benchmarks/emm_aba/emm_aba.hq -k 6 -s hpes


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

# time AutoHyper/app/AutoHyper --nusmv benchmarks/5_planning/robotic_robustness_100.smv benchmarks/AH_formulas/5.1.hq --log --incl-forq


# time cargo run --release -- -n benchmarks/5_planning/robotic_robustness_400.smv benchmarks/5_planning/robotic_robustness_400.smv -f benchmarks/5_planning/robotic_robustness_formula.hq -k 40 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/5_planning/robotic_robustness_400.smv benchmarks/AH_formulas/5.1.hq --log --incl-forq


# time cargo run --release -- -n benchmarks/5_planning/robotic_robustness_1600.smv benchmarks/5_planning/robotic_robustness_1600.smv -f benchmarks/5_planning/robotic_robustness_formula.hq -k 40 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/5_planning/robotic_robustness_1600.smv benchmarks/AH_formulas/5.1.hq --log --incl-forq


# time cargo run --release -- -n benchmarks/5_planning/robotic_robustness_3600.smv benchmarks/5_planning/robotic_robustness_3600.smv -f benchmarks/5_planning/robotic_robustness_formula.hq -k 120 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/5_planning/robotic_robustness_3600.smv benchmarks/AH_formulas/5.1.hq --log








#=== Shortest Path Planning ===#
# time cargo run --release -- -n benchmarks/5_planning/robotic_sp_100.smv benchmarks/5_planning/robotic_sp_100.smv -f benchmarks/5_planning/robotic_sp_formula.hq -k 20 -s hpes 

# time AutoHyper/app/AutoHyper --nusmv benchmarks/5_planning/robotic_sp_100.smv benchmarks/AH_formulas/5.2.hq --witness

# time cargo run --release -- -n benchmarks/5_planning/robotic_sp_400.smv benchmarks/5_planning/robotic_sp_400.smv -f benchmarks/5_planning/robotic_sp_formula.hq -k 40 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/5_planning/robotic_sp_400.smv benchmarks/AH_formulas/5.2.hq --log --witness

# time cargo run --release -- -n benchmarks/5_planning/robotic_sp_1600.smv benchmarks/5_planning/robotic_sp_1600.smv -f benchmarks/5_planning/robotic_sp_formula.hq -k 80 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/5_planning/robotic_sp_1600.smv benchmarks/AH_formulas/5.2.hq --log --witness

# time cargo run --release -- -n benchmarks/5_planning/robotic_sp_3600.smv benchmarks/5_planning/robotic_sp_3600.smv -f benchmarks/5_planning/robotic_sp_formula.hq -k 120 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/5_planning/robotic_sp_3600.smv benchmarks/AH_formulas/5.2.hq --log





#=== Mutation Testing ===#
# echo "mutation"
# cargo run --release -- -n benchmarks/6_mutation/mutation_testing.smv benchmarks/6_mutation/mutation_testing.smv -f benchmarks/6_mutation/mutation_testing.hq -k 10 -s pes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/6_mutation/mutation_testing.smv benchmarks/AH_formulas/6.hq


#=== Co-termination ===#
# time cargo run --release -- -n benchmarks/7_coterm/coterm1.smv benchmarks/7_coterm/coterm1.smv -f benchmarks/7_coterm/coterm.hq -k 10 -s hpes


# time AutoHyper/app/AutoHyper --nusmv benchmarks/7_coterm/coterm1.smv benchmarks/AH_formulas/7.hq






#=== Deniability ===#
# time cargo run --release -- -n benchmarks/8_deniability/electronic_wallet.smv benchmarks/8_deniability/electronic_wallet.smv benchmarks/8_deniability/electronic_wallet.smv -f benchmarks/8_deniability/den.hq -k 10 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/8_deniability/electronic_wallet.smv benchmarks/AH_formulas/8.hq --log --incl-forq



#=== Shared buffer ===#
# time cargo run --release -- -n benchmarks/9_buffer/scheduled_buffer.smv benchmarks/9_buffer/scheduled_buffer.smv -f benchmarks/9_buffer/classic_OD.hq -k 10 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/9_buffer/scheduled_buffer.smv benchmarks/AH_formulas/9.1.hq --log --witness


# time cargo run --release -- -n benchmarks/9_buffer/scheduled_buffer.smv benchmarks/9_buffer/scheduled_buffer.smv -f benchmarks/9_buffer/intrans_OD.hq -k 10 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/9_buffer/scheduled_buffer.smv benchmarks/AH_formulas/9.2.hq --log



# time cargo run --release -- -n benchmarks/9_buffer/scheduled_buffer.smv benchmarks/9_buffer/scheduled_buffer.smv -f benchmarks/9_buffer/intrans_GMNI.hq -k 10 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/9_buffer/scheduled_buffer.smv benchmarks/AH_formulas/9.3.hq --log



# time cargo run --release -- -n benchmarks/9_buffer/unscheduled_buffer.smv benchmarks/9_buffer/unscheduled_buffer.smv -f benchmarks/9_buffer/classic_OD.hq -k 10 -s hpes -c

# time AutoHyper/app/AutoHyper --nusmv benchmarks/9_buffer/unscheduled_buffer.smv benchmarks/AH_formulas/9.1.hq --log --witness



#=== Non-determinism Experience ===#
# time cargo run --release -- -n benchmarks/10_NIexp/ni_example.smv benchmarks/10_NIexp/ni_example.smv -f benchmarks/10_NIexp/tini.hq -k 10 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/10_NIexp/ni_example.smv benchmarks/AH_formulas/10.1.hq --log --incl-forq



# time cargo run --release -- -n benchmarks/10_NIexp/ni_example.smv benchmarks/10_NIexp/ni_example.smv -f benchmarks/10_NIexp/tsni.hq -k 10 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/10_NIexp/ni_example.smv benchmarks/AH_formulas/10.2.hq --log --incl-forq



#=== k-safety ===#
# time cargo run --release -- -n benchmarks/11_ksafety/doubleSquare.smv benchmarks/11_ksafety/doubleSquare.smv -f benchmarks/11_ksafety/doubleSquare.hq -k 50 -s hpes -c


# time AutoHyper/app/AutoHyper --nusmv benchmarks/11_ksafety/doubleSquare.smv benchmarks/AH_formulas/11.hq --log



#=== Mapping synthesis ===#
# time cargo run --release -- -n benchmarks/12_mapsynth/msynth_MM.smv  benchmarks/12_mapsynth/msynth_MA.smv benchmarks/12_mapsynth/msynth_MB.smv benchmarks/12_mapsynth/msynth_MA.smv benchmarks/12_mapsynth/msynth_MB.smv -f benchmarks/12_mapsynth/msynth.hq -k 10 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/12_mapsynth/msynth_MM.smv  benchmarks/12_mapsynth/msynth_MA.smv benchmarks/12_mapsynth/msynth_MB.smv benchmarks/12_mapsynth/msynth_MA.smv benchmarks/12_mapsynth/msynth_MB.smv benchmarks/AH_formulas/12.1.hq --log



# time cargo run --release -- -n benchmarks/12_mapsynth/msynth2_MM.smv  benchmarks/12_mapsynth/msynth2_MA.smv benchmarks/12_mapsynth/msynth2_MB.smv benchmarks/12_mapsynth/msynth2_MA.smv benchmarks/12_mapsynth/msynth2_MB.smv -f benchmarks/12_mapsynth/msynth2.hq -k 10 -s hpes


# time AutoHyper/app/AutoHyper --nusmv benchmarks/12_mapsynth/msynth2_MM.smv  benchmarks/12_mapsynth/msynth2_MA.smv benchmarks/12_mapsynth/msynth2_MB.smv benchmarks/12_mapsynth/msynth2_MA.smv benchmarks/12_mapsynth/msynth2_MB.smv benchmarks/AH_formulas/12.2.hq --log --incl-forq




#=== TEAM LTL ===#
# time cargo run --release -- -n benchmarks/13_teamltl/team.smv benchmarks/13_teamltl/team.smv benchmarks/13_teamltl/team.smv -f benchmarks/13_teamltl/team.hq -k 10 -s hpes


# time AutoHyper/app/AutoHyper --nusmv benchmarks/13_teamltl/team.smv benchmarks/AH_formulas/13.1.hq --log


# time cargo run --release -- -n benchmarks/13_teamltl/team2.smv benchmarks/13_teamltl/team2.smv benchmarks/13_teamltl/team2.smv -f benchmarks/13_teamltl/team.hq -k 21 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/13_teamltl/team2.smv benchmarks/AH_formulas/13.2.hq --log


#=== NDET ===#
# time cargo run --release -- -n benchmarks/14_ndet/NI_v1.smv benchmarks/14_ndet/NI_v1.smv -f benchmarks/14_ndet/NI.hq -k 10 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/14_ndet/NI_v1.smv benchmarks/AH_formulas/14.hq --log --witness --incl-forq 

# time cargo run --release -- -n benchmarks/14_ndet/NI_v2.smv benchmarks/14_ndet/NI_v2.smv -f benchmarks/14_ndet/NI.hq -k 10 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/14_ndet/NI_v2.smv benchmarks/AH_formulas/14.hq --log --witness --incl-forq

# time cargo run --release -- -n benchmarks/14_ndet/NI_v3.smv benchmarks/14_ndet/NI_v3.smv -f benchmarks/14_ndet/NI.hq -k 10 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/14_ndet/NI_v3.smv benchmarks/AH_formulas/14.hq --log --incl-forq



#=== Bank ===#

# time cargo run --release -- -n benchmarks/15_bank/bank3_complex_V1.smv benchmarks/15_bank/bank3_complex_V1.smv benchmarks/15_bank/bank3_complex_V1.smv -f benchmarks/15_bank/gmni.hq -k 10 -s hpes -q

# time AutoHyper/app/AutoHyper --nusmv benchmarks/15_bank/bank3_complex_V1.smv benchmarks/AH_formulas/15.hq --log --witness

# time cargo run --release -- -n benchmarks/15_bank/bank3_complex_V2.smv benchmarks/15_bank/bank3_complex_V2.smv benchmarks/15_bank/bank3_complex_V2.smv -f benchmarks/15_bank/gmni.hq -k 10 -s hpes -q

# time AutoHyper/app/AutoHyper --nusmv benchmarks/15_bank/bank3_complex_V2.smv benchmarks/AH_formulas/15.hq --log --witness

# time cargo run --release -- -n benchmarks/15_bank/bank3_complex_V3.smv benchmarks/15_bank/bank3_complex_V3.smv benchmarks/15_bank/bank3_complex_V3.smv -f benchmarks/15_bank/gmni.hq -k 10 -s hpes -q

# time AutoHyper/app/AutoHyper --nusmv benchmarks/15_bank/bank3_complex_V3.smv benchmarks/AH_formulas/15.hq --log --witness




#=== Constructor ===#

# time cargo run --release -- -n benchmarks/sync/16_constructor/constructor_conc.smv benchmarks/sync/16_constructor/constructor_seq.smv -f benchmarks/sync/16_constructor/Linearizability.hq -k 10 -s hpes

# time AutoHyper/app/AutoHyper --nusmv benchmarks/16_constructor/constructor_conc.smv benchmarks/16_constructor/constructor_seq.smv benchmarks/AH_formulas/16.hq --log --witness



#=== TicTac ===#

### TODO: line 44 is to be fixed
# time cargo run --release -- -n benchmarks/17_tictac/tictac.smv benchmarks/17_tictac/tictac.smv -f benchmarks/17_tictac/determinism.hq -k 20 -s hpes



#=== bidding ===#

# time cargo run --release -- -n benchmarks/18_bidding/bid_safe.smv benchmarks/18_bidding/bid_safe.smv -f benchmarks/18_bidding/bidding.hq -k 10 -s hpes -q

# time AutoHyper/app/AutoHyper --nusmv benchmarks/18_bidding/bid_safe.smv  benchmarks/AH_formulas/18.hq --log


# time cargo run --release -- -n benchmarks/18_bidding/bid_safe_2.smv benchmarks/18_bidding/bid_safe_2.smv -f benchmarks/18_bidding/bidding.hq -k 10 -s hpes -q

# time AutoHyper/app/AutoHyper --nusmv benchmarks/18_bidding/bid_safe_2.smv  benchmarks/AH_formulas/18.hq --log


# time cargo run --release -- -n benchmarks/18_bidding/bid_safe_4.smv benchmarks/18_bidding/bid_safe_4.smv -f benchmarks/18_bidding/bidding.hq -k 10 -s hpes -q

# time AutoHyper/app/AutoHyper --nusmv benchmarks/18_bidding/bid_safe_4.smv  benchmarks/AH_formulas/18.hq --log


# time cargo run --release -- -n benchmarks/18_bidding/bid_unsafe.smv benchmarks/18_bidding/bid_unsafe.smv -f benchmarks/18_bidding/bidding.hq -k 10 -s hpes -q

# time AutoHyper/app/AutoHyper --nusmv benchmarks/18_bidding/bid_unsafe.smv  benchmarks/AH_formulas/18.hq --log --witness



#=== IQueue ===#

# time cargo run --release -- -n benchmarks/19_iqueue/iqueue_conc.smv benchmarks/19_iqueue/iqueue_seq.smv -f benchmarks/19_iqueue/iqueue.hq -k 10 -s hpes -q

# time AutoHyper/app/AutoHyper --nusmv benchmarks/19_iqueue/iqueue_conc.smv benchmarks/19_iqueue/iqueue_seq.smv  benchmarks/AH_formulas/19.hq --log --witness



#=== Keypad ===#


# time cargo run --release -- -n benchmarks/20_keypad/keypad.smv benchmarks/20_keypad/keypad.smv -f benchmarks/20_keypad/keypad_2.hq -k 10 -s hpes -q

# time AutoHyper/app/AutoHyper --nusmv benchmarks/20_keypad/keypad.smv benchmarks/AH_formulas/20.hq --log --witness



#=== Queue ===#

# time cargo run --release -- -n benchmarks/21_queue/concurrent.smv benchmarks/21_queue/atomic.smv -f benchmarks/21_queue/lin.hq -k 10 -s hpes 


# time AutoHyper/app/AutoHyper --nusmv benchmarks/21_queue/concurrent.smv benchmarks/21_queue/atomic.smv benchmarks/AH_formulas/21.hq --log 




#=== EMM_ABA ===#

# time cargo run --release -- -n benchmarks/22_emm_aba/emm_aba_conc.smv benchmarks/22_emm_aba/emm_aba_seq.smv -f benchmarks/22_emm_aba/emm_aba.hq -k 6 -s hpes -q


# time AutoHyper/app/AutoHyper --nusmv benchmarks/22_emm_aba/emm_aba_conc.smv benchmarks/22_emm_aba/emm_aba_seq.smv benchmarks/AH_formulas/22.hq --log --witness --incl-forq 


#=== Lazy list ===#

# time cargo run --release -- -n benchmarks/23_lazy_list/lazy_list_conc.smv benchmarks/23_lazy_list/lazy_list_seq.smv -f benchmarks/23_lazy_list/lazy_list.hq -k 13 -s hpes 


# time AutoHyper/app/AutoHyper --nusmv benchmarks/23_lazy_list/lazy_list_conc.smv benchmarks/23_lazy_list/lazy_list_seq.smv benchmarks/AH_formulas/23.hq --log --incl-forq




#=== LOOP CONDITIONS EXAMPLES ===#

# cargo run --release -- -n benchmarks/loop_conditions/abp/abp_1.smv benchmarks/loop_conditions/abp/abp_2.smv -f benchmarks/loop_conditions/abp/abp.hq -l

# cargo run --release -- -n benchmarks/loop_conditions/abp/abp_1_buggy.smv benchmarks/loop_conditions/abp/abp_2_buggy.smv -f benchmarks/loop_conditions/abp/abp.hq -l

# cargo run --release -- -n benchmarks/loop_conditions/mm/mm1.smv benchmarks/loop_conditions/mm/mm2.smv -f benchmarks/loop_conditions/mm/mm.hq -l

#cargo run --release -- -n benchmarks/loop_conditions/mm/mm1_buggy.smv benchmarks/loop_conditions/mm/mm2_buggy.smv -f benchmarks/loop_conditions/mm/mm.hq -l

#cargo run --release -- -n benchmarks/loop_conditions/cbf/cbf1.smv benchmarks/loop_conditions/cbf/cbf2.smv -f benchmarks/loop_conditions/cbf/cbf.hq -l

# cargo run --release -- -n benchmarks/loop_conditions/cbf/cbf1_buggy.smv benchmarks/loop_conditions/cbf/cbf2_buggy.smv -f benchmarks/loop_conditions/cbf/cbf.hq -l

# cargo run --release -- -n benchmarks/loop_conditions/robust_path_planning/rp_1.smv benchmarks/loop_conditions/robust_path_planning/rp_2.smv -f benchmarks/loop_conditions/robust_path_planning/rp.hq -l

# cargo run --release -- -n benchmarks/loop_conditions/robust_path_planning/rp_1_no_sol.smv benchmarks/loop_conditions/robust_path_planning/rp_2.smv -f benchmarks/loop_conditions/robust_path_planning/rp.hq -l

# cargo run --release -- -n benchmarks/loop_conditions/simple_loop/simple_loop1.smv benchmarks/loop_conditions/simple_loop/simple_loop2.smv -f benchmarks/loop_conditions/simple_loop/simple_loop.hq -l

# cargo run --release -- -n benchmarks/loop_conditions/test_loop/rs1.smv benchmarks/loop_conditions/test_loop/rs2.smv -f benchmarks/loop_conditions/test_loop/rs.hq -l

# cargo run --release -- -n benchmarks/loop_conditions/gcw/gcw1.smv benchmarks/loop_conditions/gcw/gcw2.smv -f benchmarks/loop_conditions/gcw/gcw.hq -l

# cargo run --release -- -n benchmarks/loop_conditions/gcw/gcw1_buggy.smv benchmarks/loop_conditions/gcw/gcw2_buggy.smv -f benchmarks/loop_conditions/gcw/gcw.hq -l

# cargo run --release -- -n benchmarks/loop_conditions/simple_loop/simple_loop1.smv benchmarks/loop_conditions/simple_loop/simple_loop2.smv -f benchmarks/loop_conditions/simple_loop/simple_loop.hq -l

#  cargo run --release -- -n benchmarks/loop_conditions/test_loop/rs1.smv benchmarks/loop_conditions/test_loop/rs2.smv -f benchmarks/loop_conditions/test_loop/rs.hq -l



#=== VERLIOG EXAMPLES ===#

# RUST_BACKTRACE=1 cargo run --release -- -v verilog_benchmarks/build_infoflow.ys verilog_benchmarks/build_infoflow.ys -t main -o model.smt2 -f verilog_benchmarks/formula.hq -k 3 -s hpes

#=== LED EE===#
#cargo run --release -- -v benchmarks/verilog/LED/build_ee.ys benchmarks/verilog/LED/build_ee.ys -t light -o model.smt2 -f benchmarks/verilog/LED/formula_ee_t.hq -k 101 -s hpes

#cargo run --release -- -v benchmarks/verilog/LED/build_ee.ys benchmarks/verilog/LED/build_ee.ys -t light -o model.smt2 -f benchmarks/verilog/LED/formula_ee_f.hq -k 101 -s pes

#=== LED AE ===#
#cargo run --release -- -v benchmarks/verilog/LED/build_ae.ys benchmarks/verilog/LED/build_ae.ys -t led_fsm -o model.smt2 -f benchmarks/verilog/LED/formula_ae.hq -k 10 -s pes -c

#=== LED EA ===#
#cargo run --release -- -v benchmarks/verilog/LED/build_ea.ys benchmarks/verilog/LED/build_ea.ys -t led_fsm -o model.smt2 -f benchmarks/verilog/LED/formula_ea.hq -k 101 -s pes -c

#=== SPI ===#
# cargo run --release -- -v benchmarks/verilog/SPI/spi_build.ys benchmarks/verilog/SPI/spi_build.ys -t SPISlave -o spi.smt2 -f benchmarks/verilog/SPI/formula.hq -k 8 -s hpes

#=== fpu2 ===#
#  RUST_BACKTRACE=full cargo run --release -- -v benchmarks/verilog/divider/divider.ys benchmarks/verilog/divider/divider.ys -t divider -o model.smt2 -f benchmarks/verilog/divider/formula.hq -k 8 -s pes


#=== A-HLTL cases ===#

# #=== Test ===#

# time cargo run --release -- -n benchmarks/async/0_test/m1.smv benchmarks/async/0_test/m1.smv -f benchmarks/async/0_test/formula.hq -k 2 -m 4 -s hpes -q


#=== ACDB original ===#
# cargo run --release -- -n benchmarks/async/1_acdb/original/acdb_flattened.smv benchmarks/async/1_acdb/original/acdb_flattened.smv -f benchmarks/async/1_acdb/original/acdb.hq -k 6 -m 12 -s hpes  


#=== ACDB with_ndet ===#
# cargo run --release -- -n benchmarks/async/1_acdb/ndet/acdb_flattened.smv benchmarks/async/1_acdb/ndet/acdb_flattened.smv -f benchmarks/async/1_acdb/ndet/acdb_formula2.hq -k 8 -m 16 -s hpes 


# # === Concurrent Leak ===#
# cargo run --release -- -n benchmarks/async/2_concleaks/flattened/concleaks_2procs.smv benchmarks/async/2_concleaks/flattened/concleaks_2procs.smv  -f benchmarks/async/2_concleaks/flattened/od.hq -k 11 -m 22 -s hpes 

# === Concurrent Leak_ndet ===#
# cargo run --release -- -n benchmarks/async/2_concleaks/flattened/concleaks_3procs.smv benchmarks/async/2_concleaks/flattened/concleaks_3procs.smv  -f benchmarks/async/2_concleaks/flattened/od.hq -k 18 -m 36 -s hpes 


#=== Speculative Execution - V1 ===#

# time cargo run --release -- -n benchmarks/async/3_speculative/flattened/v1_se.smv benchmarks/async/3_speculative/flattened/v1_nse.smv -f benchmarks/async/3_speculative/flattened/se_prop.hq -k 6 -m 12 -s hpes 

# time cargo run --release -- -n benchmarks/async/3_speculative/flattened/model_flattened.smv benchmarks/async/3_speculative/flattened/model_flattened -f benchmarks/async/3_speculative/flattened/se_prop.hq -k 6 -m 12 -s hpes 

#=== Speculative Execution - V2 ===#

# time cargo run --release -- -n benchmarks/async/3_speculative/flattened/v2_se.smv benchmarks/async/3_speculative/flattened/v2_nse.smv -f benchmarks/async/3_speculative/flattened/se_prop.hq -k 6 -m 12 -s hpes 

# #=== Speculative Execution - V3 ===#

# time cargo run --release -- -n benchmarks/async/3_speculative/flattened/v3_se.smv benchmarks/async/3_speculative/flattened/v3_nse.smv -f benchmarks/async/3_speculative/flattened/se_prop.hq -k 6 -m 12 -s hpes 

#=== Speculative Execution - V4 ===#

# time cargo run --release -- -n benchmarks/async/3_speculative/flattened/v4_se.smv benchmarks/async/3_speculative/flattened/v4_nse.smv -f benchmarks/async/3_speculative/flattened/se_prop.hq -k 6 -m 12 -s hpes 


#=== Speculative Execution - V5 ===#

# time cargo run --release -- -n benchmarks/async/3_speculative/flattened/v5_se.smv benchmarks/async/3_speculative/flattened/v5_nse.smv -f benchmarks/async/3_speculative/flattened/se_prop.hq -k 6 -m 12 -s hpes 


#=== Speculative Execution - V6 ===#

# time cargo run --release -- -n benchmarks/async/3_speculative/flattened/v6_se.smv benchmarks/async/3_speculative/flattened/v6_nse.smv -f benchmarks/async/3_speculative/flattened/se_prop.hq -k 6 -m 12 -s hpes 


#=== Speculative Execution - V7 ===#

# time cargo run --release -- -n benchmarks/async/3_speculative/flattened/v7_se.smv benchmarks/async/3_speculative/flattened/v7_nse.smv -f benchmarks/async/3_speculative/flattened/se_prop.hq -k 6 -m 12 -s hpes 


#=== Optimization - DBE ===#
# time cargo run --release -- -n benchmarks/async/4_optimization/original/dbe/DBE_source.smv benchmarks/async/4_optimization/original/dbe/DBE_target.smv -f benchmarks/async/4_optimization/original/dbe/DBE.hq -k 4 -m 8 -s hpes 


#=== Optimization - DBE_ndet ===#
# time cargo run --release -- -n benchmarks/async/4_optimization/with_ndet/dbe/DBE_source_ndet.smv benchmarks/async/4_optimization/with_ndet/dbe/DBE_target_ndet.smv -f benchmarks/async/4_optimization/with_ndet/dbe/DBE.hq -k 13 -m 26 -s hpes 

#=== Optimization - DBE_ndet_bug ===#
# time cargo run --release -- -n benchmarks/async/4_optimization/with_ndet/dbe/DBE_source_ndet.smv benchmarks/async/4_optimization/with_ndet/dbe/DBE_target_wrong_ndet.smv -f benchmarks/async/4_optimization/with_ndet/dbe/DBE.hq -k 13 -m 26 -s hpes 


#=== Optimization - LP ===#
# time cargo run --release -- -n benchmarks/async/4_optimization/original/lp/LP_source.smv benchmarks/async/4_optimization/original/lp/LP_target.smv -f benchmarks/async/4_optimization/original/lp/LP.hq -k 23 -m 45 -s hpes -q


#=== Optimization - LP_ndet ===#
# time cargo run --release -- -n benchmarks/async/4_optimization/with_ndet/lp/LP_source_ndet.smv benchmarks/async/4_optimization/with_ndet/lp/LP_target_wrong_ndet.smv -f benchmarks/async/4_optimization/with_ndet/lp/LP.hq -k 17 -m 34 -s hpes 


#=== Optimization - LP_loop ===#
# time cargo run --release -- -n benchmarks/async/4_optimization/with_loops/lp/LP_source_ndet.smv benchmarks/async/4_optimization/with_loops/lp/LP_target_ndet.smv -f benchmarks/async/4_optimization/with_loops/lp/LP.hq -k 35 -m 70 -s hpes 


#=== Optimization - LP_loop_buggy ===#
# time cargo run --release -- -n benchmarks/async/4_optimization/with_loops/lp/LP_source_ndet.smv benchmarks/async/4_optimization/with_loops/lp/LP_target_wrong_ndet.smv -f benchmarks/async/4_optimization/with_loops/lp/LP.hq -k 17 -m 34 -s hpes


#=== Optimization - EFLP ===#
# time cargo run --release -- -n benchmarks/async/4_optimization/original/eflp/EFLP_source.smv benchmarks/async/4_optimization/original/eflp/EFLP_target.smv -f benchmarks/async/4_optimization/original/eflp/EFLP.hq -k 32 -m 64 -s hpes -q


#=== Optimization - EFLP_ndet ===#
# time cargo run --release -- -n benchmarks/async/4_optimization/with_ndet/eflp/EFLP_source_ndet.smv benchmarks/async/4_optimization/with_ndet/eflp/EFLP_target_ndet.smv -f benchmarks/async/4_optimization/with_ndet/eflp/EFLP.hq -k 22 -m 44 -s hpes 


#=== Optimization - EFLP_ndet_loop ===#
# time cargo run --release -- -n benchmarks/async/4_optimization/with_loops/eflp/EFLP_source_ndet.smv benchmarks/async/4_optimization/with_loops/eflp/EFLP_target_ndet.smv -f benchmarks/async/4_optimization/with_loops/eflp/EFLP.hq -k 45 -m 90 -s hpes 



#=== CACHE ===#
# time cargo run --release -- -n benchmarks/async/5_cache/cache_flattened.smv benchmarks/async/5_cache/cache_flattened.smv -f benchmarks/async/5_cache/odnd.hq -k 13 -m 26 -s hpes 


