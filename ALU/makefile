#Define variables
SRC_FILES = filelist.f
#SRC_FILES = error_injection/filelist.f
#TB_FILES = mypkg.sv mytop.sv


#Flags
VCS_FLAGS = -sverilog -debug_access+all -cm line+cond+tgl+branch -f
DVE_FLAGS = -cm line+cond+tgl+branch
URG_FLAGS = -dir simv.vdb -format both

#Default target
all: clean compile simulate generate

# clean files 
clean:
	@echo "Cleaning up..."
	rm -rf csrc *.vcd *.vpd *.log *.key DVEfiles simv.daidir urgReport *.tar.gz

#compile the design
compile:  
	@echo "Start compile..."
	vcs $(VCS_FLAGS) $(SRC_FILES) -o simv 

#simulate the design
simulate:
	@echo "Starting simulation..."
	./simv $(DVE_FLAGS)
 
#generating reports
generate:
	@echo "Running coverage reports..."
	urg  $(URG_FLAGS) -elfile exec.el


#open coverage reports
#open_coverage_reports:
#	@echo "open coverage reports..." 
#	gedit urgReport/grpinfo.txt &
