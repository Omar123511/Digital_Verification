######################################################################
## file Name: Makefile 
## Engineer : Omnia Mohamed
## Date: May 2025
## Description: 
##    This makefile is used to compile, run all tests and merge the coverge of all tests using vcs.
######################################################################
SIM = ./simulation
LOG_FILES = $(SIM)/log_files
VDB_FILES = $(SIM)/vdb_files
TESTS =  Base_Test R_Type_Test1 I_Type_Reg_Test1 I_Type_Load_Test  S_Type_Test Store_Load_Test U_Type_Test M_Extension_Test B_Type_Test Jump_Test Rand_Test All_Ones_Test Zeros_Ones_Test Max_Min_Test  Signed_Max_Test Signed_Min_Test Hazard_Test 

#Base_Test R_Type_Test1 I_Type_Reg_Test1 I_Type_Load_Test  S_Type_Test Store_Load_Test U_Type_Test M_Extension_Test B_Type_Test Jump_Test Rand_Test All_Ones_Test Zeros_Ones_Test Max_Min_Test  Signed_Max_Test Signed_Min_Test Hazard_Test



all: comp run merge cov_dve
#clean comp run merge cov_dve

clean:
	rm -rf simv* csrc* *.vcd *.log $(LOG_FILES) urgReport novas* DVEfiles $(VDB_FILES) ./simulation/*.vdb *.vpd *.vdb $(SIM)/merged_coverage_report/  vdCovLog  vfastLog verdi* *.key *.h
comp:
	mkdir -p $(LOG_FILES)
	mkdir -p $(VDB_FILES)
	vcs -sverilog -debug_access+all   -ntb_opts uvm +ntb_random_seed=100 -timescale=1ns/1ps  -cm line+tgl+branch+cond -cm_hier cov_hier.f -cm_assert_hier sva_cov_path.f -cm_dir $(VDB_FILES)/compile_cov  -f rtl_file_list.txt  -f tb_comp_list.txt -l $(LOG_FILES)/comp.log
run:
	@for test in $(TESTS); do \
	./simv  +UVM_TESTNAME=$$test +UVM_VERBOSITY=UVM_NONE -cm line+tgl+branch+cond  -cm_dir $(VDB_FILES)/$$test -l $(LOG_FILES)/$$test.log ;\
	done
run_gui:
	@for test in $(TESTS); do \
	./simv -gui  +UVM_TESTNAME=$$test +UVM_VERBOSITY=UVM_NONE -cm line+tgl+branch+cond -cm_dir $(VDB_FILES)/$$test -l $(LOG_FILES)/$$test.log ;\
	done
merge:
	urg  -dir $(VDB_FILES)/*.vdb  -dbname Merged_db -elfile rtl_out_of_scope_exclusion.el -report $(SIM)/merged_coverage_report -format both
cov_dve:
	dve -cov -dir Merged_db.vdb -elfile rtl_out_of_scope_exclusion.el &
cov_verdi:
	verdi -cov -covdir Merged_db.vdb -elfile rtl_out_of_scope_exclusion.el &


