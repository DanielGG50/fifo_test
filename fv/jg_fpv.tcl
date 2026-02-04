clear -all

set_proofgrid_bridge off

analyze -sv12 ../rtl/sfifo.sv
analyze -sv12 property_defines.svh
analyze -sv12 +define+SFIFO_TOP fv_sfifo.sv

elaborate  -bbox_a 65535 -bbox_mul 65535 -top sfifo

clock clk
reset -expression !arst_n

set_engineJ_max_trace_length 2000
