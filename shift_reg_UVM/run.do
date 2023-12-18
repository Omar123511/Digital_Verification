vlib work
vsim -voptargs=+acc work.top -classdebug -uvmcontrol=all
add wave /top/shift_regif/*
run -all