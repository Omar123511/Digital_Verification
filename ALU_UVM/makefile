#Define variables
SRC_FILES = filelist.f
UVM_HOME = UVM_HOME
#SRC_FILES = error_injection/filelist.f
#TB_FILES = mypkg.sv mytop.sv


#Flags
#VCS_FLAGS = -full64 -sverilog -debug_access+all -ntb_opts uvm -timescale=1ns/1ps -cm line+cond+tgl+branch -f $(SRC_FILES) -top my_top +incdir+$$UVM_HOME/src

VCS_FLAGS = -full64 -sverilog -debug_access+all -ntb_opts uvm -timescale=1ns/1ps -cm line+cond+tgl+branch -f $(SRC_FILES) -top my_top

DVE_FLAGS = -cm line+cond+tgl+branch

TEST_NAME = my_test
VERBOSITY_LEVEL = MEDIUM

UVM_SIM = +UVM_TESTNAME="$(TEST_NAME)" +UVM_VERBOSITY=UVM_$(VERBOSITY_LEVEL) +access+r
URG_FLAGS = -dir simv.vdb -format both -elfile exec.el

#Default target
all: clean compile simulate generate

# clean files 
clean:
	@echo "Cleaning up..."
	rm -rf csrc *.vcd *.vpd *.log *.key DVEfiles simv.daidir urgReport *.tar.gz

#compile the design
compile:  
	@echo "Start compile..."
	vcs $(VCS_FLAGS) -o simv 

#simulate the design
simulate:
	@echo "Starting simulation..."
	./simv $(DVE_FLAGS) $(UVM_SIM)
 
#generating reports
generate:
	@echo "Running coverage reports..."
	urg  $(URG_FLAGS)


#open coverage reports
#open_coverage_reports:
#	@echo "open coverage reports..." 
#	gedit urgReport/grpinfo.txt &
