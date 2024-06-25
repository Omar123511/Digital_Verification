vlib work
vlog -work work interface.sv counter.sv pack.sv counter_tb.sv SVA.sv top.sv +cover -covercells
vsim -voptargs=+acc work.top -cover
add wave *
add wave -position insertpoint sim:/top/DUT/SVA_inst0/data_load_inactive_3_assertion 
coverage save -du work.counter counter_tb.ucdb -onexit
run -all

