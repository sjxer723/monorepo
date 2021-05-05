onerror {exit -code 1}
vlib work
vlog -work work sc_computer.vo
vlog -work work sc_computer_test_wave_02.vwf.vt
vsim -c -t 1ps -L cycloneive_ver -L altera_ver -L altera_mf_ver -L 220model_ver -L sgate_ver -L altera_lnsim_ver work.sc_computer_vlg_vec_tst
vcd file -direction single_period_cpu_with_IO.msim.vcd
vcd add -internal sc_computer_vlg_vec_tst/*
vcd add -internal sc_computer_vlg_vec_tst/i1/*
proc simTimestamp {} {
    echo "Simulation time: $::now ps"
    if { [string equal running [runStatus]] } {
        after 2500 simTimestamp
    }
}
after 2500 simTimestamp
run -all
quit -f

