vlib work
vlog counter.sv counter_tb.sv  +cover
vsim -voptargs=+acc work.counter_tb -cover
add wave *  
coverage save -du work.counter counter_tb.ucdb -onexit
run -all