`include "mesi_isc_tb_define.v"
//`include "mesi_isc_tb.v"
//`include "mesi_isc_tb_cpu.v"

module cpu_sva (
	input clk,
	input rst,
	input [3:0] cache_state_cpu0,
	input [3:0] cache_state_cpu1,
	input [3:0] cache_state_cpu2,
	input [3:0] cache_state_cpu3
);

/*
property p_cpu0_c0_only_m;
	@(posedge clk) disable iff(rst)
		(cache_state_cpu0 ==`MESI_ISC_TB_CPU_MESI_M) |-> ((cache_state_cpu1 ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2 ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3 ==`MESI_ISC_TB_CPU_MESI_I));
endproperty
ap_cpu0_c0_only_m: assert property (p_cpu0_c0_only_m);
*/

property p_cpu0_c1_only_m;
	@(posedge clk) disable iff(rst)
		(cache_state_cpu0 ==`MESI_ISC_TB_CPU_MESI_M) |-> ((cache_state_cpu1 ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2 ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3 ==`MESI_ISC_TB_CPU_MESI_I));
endproperty
ap_cpu0_c1_only_m: assert property (p_cpu0_c1_only_m);

ap_rst: assert property (@(clk) disable iff(!rst) !rst |=> cache_state_cpu0 == 0); 

endmodule 

module cpu_sva_wrapper;
	bind mesi_isc_tb cpu_sva wrp (
		.clk(clk),
		.rst(rst),
		.cache_state_cpu0(mesi_isc_tb_cpu0.cache_state1),
		.cache_state_cpu1(mesi_isc_tb_cpu1.cache_state1),
		.cache_state_cpu2(mesi_isc_tb_cpu2.cache_state1),
		.cache_state_cpu3(mesi_isc_tb_cpu3.cache_state1)

);
endmodule
