vlib work
vlog -work work interface.sv AES.sv my_package.sv top.sv +cover -covercells
vsim -voptargs=+acc work.top -classdebug -uvmcontrol=all -cover
add wave top/AES_inf/*
coverage save -du work.AES_Encrypt top.ucdb -onexit
run -all

