`include "mesi_isc_tb_define.v"

module cpu_sva (
	input clk,
	input rst,
	input [3:0] cache_state_cpu0 [9:0],
	input [3:0] cache_state_cpu1 [9:0],
	input [3:0] cache_state_cpu2 [9:0],
	input [3:0] cache_state_cpu3 [9:0]
);

/*
assert_implication cpu0_cache_state_1_M (clk, ~rst, cache_state_cpu0[1] ==`MESI_ISC_TB_CPU_MESI_M, ((cache_state_cpu1[1] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2[1] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3[1] ==`MESI_ISC_TB_CPU_MESI_I)));
*/

/*
assert_implication cpu1_cache_state_1_M (clk, ~rst, cache_state_cpu1[1] ==`MESI_ISC_TB_CPU_MESI_M, ((cache_state_cpu0[1] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2[1] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3[1] ==`MESI_ISC_TB_CPU_MESI_I)));
*/

generate
	for(genvar i = 0; i < 9; i++) begin
	assert_implication cpu0_cache_state_M (clk, ~rst, cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_M, ((cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_I)));
	assert_implication cpu0_cache_state_E (clk, ~rst, cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_E, ((cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_I)));
end
endgenerate

generate
	for(genvar i = 0; i < 9; i++) begin
	assert_implication cpu1_cache_state_M (clk, ~rst, cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_M, ((cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_I)));
	assert_implication cpu1_cache_state_E (clk, ~rst, cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_E, ((cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_I)));
end
endgenerate

generate
	for(genvar i = 0; i < 9; i++) begin
	assert_implication cpu2_cache_state_M (clk, ~rst, cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_M, ((cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_I)));
	assert_implication cpu2_cache_state_E (clk, ~rst, cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_E, ((cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_I)));
end
endgenerate

generate
	for(genvar i = 0; i < 9; i++) begin
	assert_implication cpu3_cache_state_M (clk, ~rst, cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_M, ((cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_I)));
	assert_implication cpu3_cache_state_E (clk, ~rst, cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_E, ((cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_I)));
end
endgenerate
 
endmodule 

module cpu_sva_wrapper;

cpu_sva inst1 (
		.clk(tb.clk),
		.rst(tb.rst),
		.cache_state_cpu0(tb.mesi_isc_tb_cpu0.cache_state),
		.cache_state_cpu1(tb.mesi_isc_tb_cpu1.cache_state),
		.cache_state_cpu2(tb.mesi_isc_tb_cpu2.cache_state),
		.cache_state_cpu3(tb.mesi_isc_tb_cpu3.cache_state)
        );
endmodule
