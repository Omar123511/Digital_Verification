vlib work
quit -sim
vlib work
vlog -define SIM fifo_interface.sv shared_pkg.sv pkg_trans.sv pkg_coverage.sv FIFO_scoreboard_pkg.sv monitor.sv FIFO.sv FIFO_golden_model.sv fifo_tb.sv top_fifo.sv +cover 
vsim -voptargs=+acc work.top -cover
add wave *
add wave -position insertpoint  \
sim:/top/fifoif/* \
sim:/DUT/count \
sim:/top/mon/score
add wave /top/DUT/a1 /top/DUT/a2 /top/DUT/a3 /top/DUT/a4 /top/DUT/a5 /top/DUT/a6 /top/DUT/a7 /top/DUT/a8 /top/DUT/a9 
coverage save FIFO.ucdb -onexit -du work.FIFO
run -all