vlib work
vlog counter_if.sv monitor.sv package.sv top.sv counter_sva.sv counter.sv counter_tb.sv +cover
vlog -work work -vopt +incdir+path_to_assertions_dir +define+SIM counter.sv
vsim -voptargs=+acc work.top -cover
add wave /top/counterif/*
add wave /top/tb/*
add wave /top/DUT/countersva/assert_load_p /top/DUT/countersva/assert_int_cnt_p /top/DUT/countersva/assert_dec_cnt_p
run -all
coverage save top.ucdb -du work.counter -onexit
