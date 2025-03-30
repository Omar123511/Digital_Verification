vlib work
vlog -work work interface.sv memory.sv my_package.sv top.sv +cover -covercells
vsim -voptargs=+acc work.top -classdebug -uvmcontrol=all -cover
add wave top/mem_inf/*
coverage save -du work.memory top.ucdb -onexit
run -all

