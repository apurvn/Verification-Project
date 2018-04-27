`include "mesi_isc_tb_define.v"

module cpu_sva (
	input clk,
	input rst,
	input [3:0] cache_state
);

assert property (@(posedge clk) $fell(rst) |-> cache_state == `MESI_ISC_TB_CPU_MESI_I); 

endmodule 

//module cpu_sva_wrapper;
//	bind mesi_isc_tb_cpu cpu_sva wrp (
//		.clk(tb.clk),
//		.rst(tb.rst),
//		.cache_state(mesi_isc_tb.mesi_isc_tb_cpu3.cache_state)
//);
//endmodule
