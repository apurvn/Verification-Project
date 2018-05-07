`include "mesi_isc_tb_define.v"

module cpu_sva (
	input clk,
	input rst,
	input [3:0] cache_state_cpu0 [9:0],
	input [3:0] cache_state_cpu1 [9:0],
	input [3:0] cache_state_cpu2 [9:0],
	input [3:0] cache_state_cpu3 [9:0],
    	input [3:0] c_state,
    	input [2:0] m_state,
    	input m_state_c_state_priority,
    	input wr_proc_wait_for_en,
    	input rd_proc_wait_for_en,
    	input [3:0] tb_ins_i,
    	input [3:0] tb_ins_addr_i
);
/********************* check in rst ********************/
generate 
	for(genvar i=0; i <= 9; i++) begin
	assert_implication cpu0_rst_cache_state (clk, rst, (rst == 1),(cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_I));
end
endgenerate

generate 
	for(genvar i=0; i <= 9; i++) begin
	assert_implication cpu1_rst_cache_state (clk, rst, (rst == 1),(cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_I));
end
endgenerate

generate 
	for(genvar i=0; i <= 9; i++) begin
	assert_implication cpu2_rst_cache_state (clk, rst, (rst == 1),(cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_I));
end
endgenerate

generate 
	for(genvar i=0; i <= 9; i++) begin
	assert_implication cpu3_rst_cache_state (clk, rst, (rst == 1),(cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_I));
end
endgenerate

/*   | M  E  S  I
 * __|____________
 * M | n  n  n  y
 * E | n  n  n  y
 * S | n  n  y  y
 * I | y  y  y  y
 *   |
 */ 
/********************* check M & E *********************/
generate
	for(genvar i = 0; i <= 9; i++) begin
	assert_implication cpu0_cache_state_M (clk, ~rst, cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_M, ((cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_I)));
	assert_implication cpu0_cache_state_E (clk, ~rst, cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_E, ((cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_I)));
end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	assert_implication cpu1_cache_state_M (clk, ~rst, cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_M, ((cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_I)));
	assert_implication cpu1_cache_state_E (clk, ~rst, cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_E, ((cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_I)));
end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	assert_implication cpu2_cache_state_M (clk, ~rst, cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_M, ((cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_I)));
	assert_implication cpu2_cache_state_E (clk, ~rst, cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_E, ((cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_I)));
end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	assert_implication cpu3_cache_state_M (clk, ~rst, cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_M, ((cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_I)));
	assert_implication cpu3_cache_state_E (clk, ~rst, cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_E, ((cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_I)));
end
endgenerate
 
/********************* check S *********************/
generate
	for(genvar i = 0; i <= 9; i++) begin
	assert_implication cpu3_cache_state_S (clk, ~rst, cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_S, ((cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_I || cache_state_cpu0[i] == `MESI_ISC_TB_CPU_MESI_S) && (cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_S || cache_state_cpu1[i] == `MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_I || cache_state_cpu2[i] == `MESI_ISC_TB_CPU_MESI_S)));
end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	assert_implication cpu2_cache_state_S (clk, ~rst, cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_S, ((cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_I || cache_state_cpu0[i] == `MESI_ISC_TB_CPU_MESI_S) && (cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_S || cache_state_cpu1[i] == `MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_I || cache_state_cpu3[i] == `MESI_ISC_TB_CPU_MESI_S)));
end
endgenerate


generate
	for(genvar i = 0; i <= 9; i++) begin
	assert_implication cpu1_cache_state_S (clk, ~rst, cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_S, ((cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_I || cache_state_cpu0[i] == `MESI_ISC_TB_CPU_MESI_S) && (cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_S || cache_state_cpu2[i] == `MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_I || cache_state_cpu3[i] == `MESI_ISC_TB_CPU_MESI_S)));
end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	assert_implication cpu0_cache_state_S (clk, ~rst, cache_state_cpu0[i] ==`MESI_ISC_TB_CPU_MESI_S, ((cache_state_cpu3[i] ==`MESI_ISC_TB_CPU_MESI_I || cache_state_cpu3[i] == `MESI_ISC_TB_CPU_MESI_S) && (cache_state_cpu1[i] ==`MESI_ISC_TB_CPU_MESI_S || cache_state_cpu1[i] == `MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu2[i] ==`MESI_ISC_TB_CPU_MESI_I || cache_state_cpu2[i] == `MESI_ISC_TB_CPU_MESI_S)));
end
endgenerate

/********************* failed write starve property *********************/
//Local WR to a cache line ends the state to be in Modified
generate
	for(genvar i = 0; i <= 9; i++) begin
	write_starve_cpu0: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_WR) && (tb_ins_addr_i == i) |=>  ##[0:500] cache_state_cpu0[i] == `MESI_ISC_TB_CPU_MESI_M);
	end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	write_starve_cpu1: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_WR) && (tb_ins_addr_i == i) |=>  ##[0:500] cache_state_cpu1[i] == `MESI_ISC_TB_CPU_MESI_M);
	end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	write_starve_cpu2: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_WR) && (tb_ins_addr_i == i) |=>  ##[0:500] cache_state_cpu2[i] == `MESI_ISC_TB_CPU_MESI_M);
	end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	write_starve_cpu3: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_WR) && (tb_ins_addr_i == i) |=>  ##[0:500] cache_state_cpu3[i] == `MESI_ISC_TB_CPU_MESI_M);
	end
endgenerate

/********************* failed local rd changes from I to E property *********************/
//Local RD of an Invalid cache line changes the state to Exclusive
generate
	for(genvar i = 0; i <= 9; i++) begin
	Local_RD_ItoE_cpu0: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_RD) && (tb_ins_addr_i == i) && (cache_state_cpu0[i] == `MESI_ISC_TB_CPU_MESI_I) |=>  ##[0:500] cache_state_cpu0[i] == `MESI_ISC_TB_CPU_MESI_E);
	end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	Local_RD_ItoE_cpu1: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_RD) && (tb_ins_addr_i == i) && (cache_state_cpu1[i] == `MESI_ISC_TB_CPU_MESI_I) |=>  ##[0:500] cache_state_cpu1[i] == `MESI_ISC_TB_CPU_MESI_E);
	end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	Local_RD_ItoE_cpu2: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_RD) && (tb_ins_addr_i == i) && (cache_state_cpu2[i] == `MESI_ISC_TB_CPU_MESI_I) |=>  ##[0:500] cache_state_cpu2[i] == `MESI_ISC_TB_CPU_MESI_E);
	end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	Local_RD_ItoE_cpu3: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_RD) && (tb_ins_addr_i == i) && (cache_state_cpu3[i] == `MESI_ISC_TB_CPU_MESI_I) |=>  ##[0:500] cache_state_cpu3[i] == `MESI_ISC_TB_CPU_MESI_E);
	end
endgenerate

/********************* failed local rd changes from E to E property *********************/
//Local RD of an Exclusive cache line changes the state to Exclusive
//for most of the cache lines, Exclusive state is not reached!
generate
	for(genvar i = 0; i <= 9; i++) begin
	Local_RD_EtoE_cpu0: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_RD) && (tb_ins_addr_i == i) && (cache_state_cpu0[i] == `MESI_ISC_TB_CPU_MESI_E) |=>  ##[0:500] cache_state_cpu0[i] == `MESI_ISC_TB_CPU_MESI_E);
	end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	Local_RD_EtoE_cpu1: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_RD) && (tb_ins_addr_i == i) && (cache_state_cpu1[i] == `MESI_ISC_TB_CPU_MESI_E) |=>  ##[0:500] cache_state_cpu1[i] == `MESI_ISC_TB_CPU_MESI_E);
	end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	Local_RD_EtoE_cpu2: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_RD) && (tb_ins_addr_i == i) && (cache_state_cpu2[i] == `MESI_ISC_TB_CPU_MESI_E) |=>  ##[0:500] cache_state_cpu2[i] == `MESI_ISC_TB_CPU_MESI_E);
	end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	Local_RD_EtoE_cpu3: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_RD) && (tb_ins_addr_i == i) && (cache_state_cpu3[i] == `MESI_ISC_TB_CPU_MESI_E) |=>  ##[0:500] cache_state_cpu3[i] == `MESI_ISC_TB_CPU_MESI_E);
	end
endgenerate

/********************* failed local rd changes from S to S property *********************/
//Local RD of an Shared cache line keeps in Shared
generate
	for(genvar i = 0; i <= 9; i++) begin
	Local_RD_StoS_cpu0: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_RD) && (tb_ins_addr_i == i) && (cache_state_cpu0[i] == `MESI_ISC_TB_CPU_MESI_S) |=>  ##[0:500] cache_state_cpu0[i] == `MESI_ISC_TB_CPU_MESI_S);
	end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	Local_RD_StoS_cpu1: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_RD) && (tb_ins_addr_i == i) && (cache_state_cpu1[i] == `MESI_ISC_TB_CPU_MESI_S) |=>  ##[0:500] cache_state_cpu1[i] == `MESI_ISC_TB_CPU_MESI_S);
	end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	Local_RD_StoS_cpu2: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_RD) && (tb_ins_addr_i == i) && (cache_state_cpu2[i] == `MESI_ISC_TB_CPU_MESI_S) |=>  ##[0:500] cache_state_cpu2[i] == `MESI_ISC_TB_CPU_MESI_S);
	end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	Local_RD_StoS_cpu3: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_RD) && (tb_ins_addr_i == i) && (cache_state_cpu3[i] == `MESI_ISC_TB_CPU_MESI_S) |=>  ##[0:500] cache_state_cpu3[i] == `MESI_ISC_TB_CPU_MESI_S);
	end
endgenerate

/********************* failed local rd changes from M to M property *********************/
//Local RD of an Modified cache line keeps in Modified
generate
	for(genvar i = 0; i <= 9; i++) begin
	Local_RD_MtoM_cpu0: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_RD) && (tb_ins_addr_i == i) && (cache_state_cpu0[i] == `MESI_ISC_TB_CPU_MESI_M) |=>  ##[0:500] cache_state_cpu0[i] == `MESI_ISC_TB_CPU_MESI_M);
	end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	Local_RD_MtoM_cpu1: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_RD) && (tb_ins_addr_i == i) && (cache_state_cpu1[i] == `MESI_ISC_TB_CPU_MESI_M) |=>  ##[0:500] cache_state_cpu1[i] == `MESI_ISC_TB_CPU_MESI_M);
	end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	Local_RD_MtoM_cpu2: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_RD) && (tb_ins_addr_i == i) && (cache_state_cpu2[i] == `MESI_ISC_TB_CPU_MESI_M) |=>  ##[0:500] cache_state_cpu2[i] == `MESI_ISC_TB_CPU_MESI_M);
	end
endgenerate

generate
	for(genvar i = 0; i <= 9; i++) begin
	Local_RD_MtoM_cpu3: assert property (@(posedge clk) disable iff(rst) 
		(tb_ins_i == `MESI_ISC_TB_INS_RD) && (tb_ins_addr_i == i) && (cache_state_cpu3[i] == `MESI_ISC_TB_CPU_MESI_M) |=>  ##[0:500] cache_state_cpu3[i] == `MESI_ISC_TB_CPU_MESI_M);
	end
endgenerate

/********************* coverage *********************/

generate
    for(genvar i=0; i<=9; i++) begin
        cover_cpu0_M: cover property (@(posedge clk) cache_state_cpu0[i] == `MESI_ISC_TB_CPU_MESI_M);
        cover_cpu0_E: cover property (@(posedge clk) cache_state_cpu0[i] == `MESI_ISC_TB_CPU_MESI_E);
        cover_cpu0_S: cover property (@(posedge clk) cache_state_cpu0[i] == `MESI_ISC_TB_CPU_MESI_S);
        cover_cpu0_I: cover property (@(posedge clk) cache_state_cpu0[i] == `MESI_ISC_TB_CPU_MESI_I);
    end
endgenerate

generate
    for(genvar i=0; i<=9; i++) begin
        cover_cpu1_M: cover property (@(posedge clk) cache_state_cpu1[i] == `MESI_ISC_TB_CPU_MESI_M);
        cover_cpu1_E: cover property (@(posedge clk) cache_state_cpu1[i] == `MESI_ISC_TB_CPU_MESI_E);
        cover_cpu1_S: cover property (@(posedge clk) cache_state_cpu1[i] == `MESI_ISC_TB_CPU_MESI_S);
        cover_cpu1_I: cover property (@(posedge clk) cache_state_cpu1[i] == `MESI_ISC_TB_CPU_MESI_I);
    end
endgenerate

generate
    for(genvar i=0; i<=9; i++) begin
        cover_cpu2_M: cover property (@(posedge clk) cache_state_cpu2[i] == `MESI_ISC_TB_CPU_MESI_M);
        cover_cpu2_E: cover property (@(posedge clk) cache_state_cpu2[i] == `MESI_ISC_TB_CPU_MESI_E);
        cover_cpu2_S: cover property (@(posedge clk) cache_state_cpu2[i] == `MESI_ISC_TB_CPU_MESI_S);
        cover_cpu2_I: cover property (@(posedge clk) cache_state_cpu2[i] == `MESI_ISC_TB_CPU_MESI_I);
    end
endgenerate

generate
    for(genvar i=0; i<=9; i++) begin
        cover_cpu3_M: cover property (@(posedge clk) cache_state_cpu3[i] == `MESI_ISC_TB_CPU_MESI_M);
        cover_cpu3_E: cover property (@(posedge clk) cache_state_cpu3[i] == `MESI_ISC_TB_CPU_MESI_E);
        cover_cpu3_S: cover property (@(posedge clk) cache_state_cpu3[i] == `MESI_ISC_TB_CPU_MESI_S);
        cover_cpu3_I: cover property (@(posedge clk) cache_state_cpu3[i] == `MESI_ISC_TB_CPU_MESI_I);
    end
endgenerate

cover_nop: cover property (@(posedge clk) tb_ins_i==`MESI_ISC_TB_INS_NOP);
cover_write: cover property (@(posedge clk) tb_ins_i==`MESI_ISC_TB_INS_WR);
cover_read: cover property (@(posedge clk) tb_ins_i==`MESI_ISC_TB_INS_RD);

endmodule 

module cpu_sva_wrapper;

cpu_sva inst1 (
		.clk(tb.clk),
		.rst(tb.rst),
		.cache_state_cpu0(tb.mesi_isc_tb_cpu0.cache_state),
		.cache_state_cpu1(tb.mesi_isc_tb_cpu1.cache_state),
		.cache_state_cpu2(tb.mesi_isc_tb_cpu2.cache_state),
		.cache_state_cpu3(tb.mesi_isc_tb_cpu3.cache_state),
        	.c_state(tb.mesi_isc_tb_cpu0.c_state),
		.m_state(tb.mesi_isc_tb_cpu0.m_state),
		.m_state_c_state_priority(tb.mesi_isc_tb_cpu0.m_state_c_state_priority),
		.wr_proc_wait_for_en(tb.mesi_isc_tb_cpu0.wr_proc_wait_for_en),
		.rd_proc_wait_for_en(tb.mesi_isc_tb_cpu0.rd_proc_wait_for_en),
		.tb_ins_i(tb.mesi_isc_tb_cpu0.tb_ins_i),
		.tb_ins_addr_i(tb.mesi_isc_tb_cpu0.tb_ins_addr_i)
);

endmodule
