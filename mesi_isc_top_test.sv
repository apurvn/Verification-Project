module top_props (
     // Inputs
     clk,
     rst,
     cbus_addr,
     cbus_cmd3,
     cbus_cmd2,
     cbus_cmd1,
     cbus_cmd0,
     mbus_data_rd,
     mbus_ack,
     tb_ins_array,
     tb_ins_addr3,
     tb_ins_addr2,
     tb_ins_addr1,
     tb_ins_addr0,
     mbus_cmd_array,
     mbus_addr_array,
     mbus_data_wr_array,
     cbus_ack3,
     cbus_ack2,
     cbus_ack1,
     cbus_ack0,
     tb_ins_ack,
     cache_state_cpu0,
     cache_state_cpu1,
     cache_state_cpu2,
     cache_state_cpu3
);
   
parameter
  CBUS_CMD_WIDTH           = 3,
  ADDR_WIDTH               = 32,
  DATA_WIDTH               = 32,
  BROAD_TYPE_WIDTH         = 2,
  BROAD_ID_WIDTH           = 5,  
  BROAD_REQ_FIFO_SIZE      = 4,
  BROAD_REQ_FIFO_SIZE_LOG2 = 2,
  MBUS_CMD_WIDTH           = 3,
  BREQ_FIFO_SIZE           = 2,
  BREQ_FIFO_SIZE_LOG2      = 1;
   

input clk; 
input rst; 
input [ADDR_WIDTH-1:0] cbus_addr;
input [CBUS_CMD_WIDTH-1:0] cbus_cmd3;
input [CBUS_CMD_WIDTH-1:0] cbus_cmd2;
input [CBUS_CMD_WIDTH-1:0] cbus_cmd1;
input [CBUS_CMD_WIDTH-1:0] cbus_cmd0;
input [DATA_WIDTH-1:0] mbus_data_rd;
input [3:0] mbus_ack;
input [3:0] tb_ins_array[3:0];
input [3:0] tb_ins_addr3;
input [3:0] tb_ins_addr2;
input [3:0] tb_ins_addr1;
input [3:0] tb_ins_addr0;
input [MBUS_CMD_WIDTH-1:0] mbus_cmd_array[3:0];
input [ADDR_WIDTH-1:0] mbus_addr_array[3:0];
input [DATA_WIDTH-1:0] mbus_data_wr_array[3:0];
input cbus_ack3;
input cbus_ack2;
input cbus_ack1;
input cbus_ack0;
input [3:0] tb_ins_ack;
input [3:0] cache_state_cpu0[9:0];
input [3:0] cache_state_cpu1[9:0];
input [3:0] cache_state_cpu2[9:0];
input [3:0] cache_state_cpu3[9:0];

// Cache0 state should be either M, E, S, I
assume property (@(posedge clk) (cache_state_cpu0[0] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu0[0] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu0[0] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu0[0] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu0[1] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu0[1] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu0[1] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu0[1] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu0[2] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu0[2] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu0[2] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu0[2] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu0[3] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu0[3] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu0[3] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu0[3] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu0[4] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu0[4] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu0[4] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu0[4] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu0[5] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu0[5] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu0[5] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu0[5] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu0[6] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu0[6] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu0[6] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu0[6] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu0[7] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu0[7] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu0[7] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu0[7] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu0[8] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu0[8] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu0[8] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu0[8] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu0[9] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu0[9] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu0[9] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu0[9] == `MESI_ISC_TB_CPU_MESI_I));

// Cache1 state should be either M, E, S, I
assume property (@(posedge clk) (cache_state_cpu1[0] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu1[0] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu1[0] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu1[0] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu1[1] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu1[1] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu1[1] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu1[1] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu1[2] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu1[2] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu1[2] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu1[2] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu1[3] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu1[3] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu1[3] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu1[3] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu1[4] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu1[4] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu1[4] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu1[4] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu1[5] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu1[5] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu1[5] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu1[5] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu1[6] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu1[6] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu1[6] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu1[6] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu1[7] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu1[7] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu1[7] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu1[7] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu1[8] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu1[8] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu1[8] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu1[8] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu1[9] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu1[9] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu1[9] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu1[9] == `MESI_ISC_TB_CPU_MESI_I));

// Cache2 state should be either M, E, S, I
assume property (@(posedge clk) (cache_state_cpu2[0] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu2[0] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu2[0] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu2[0] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu2[1] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu2[1] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu2[1] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu2[1] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu2[2] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu2[2] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu2[2] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu2[2] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu2[3] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu2[3] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu2[3] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu2[3] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu2[4] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu2[4] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu2[4] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu2[4] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu2[5] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu2[5] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu2[5] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu2[5] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu2[6] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu2[6] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu2[6] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu2[6] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu2[7] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu2[7] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu2[7] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu2[7] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu2[8] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu2[8] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu2[8] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu2[8] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu2[9] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu2[9] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu2[9] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu2[9] == `MESI_ISC_TB_CPU_MESI_I));

// Cache3 state should be either M, E, S, I
assume property (@(posedge clk) (cache_state_cpu3[0] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu3[0] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu3[0] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu3[0] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu3[1] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu3[1] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu3[1] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu3[1] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu3[2] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu3[2] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu3[2] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu3[2] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu3[3] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu3[3] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu3[3] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu3[3] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu3[4] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu3[4] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu3[4] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu3[4] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu3[5] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu3[5] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu3[5] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu3[5] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu3[6] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu3[6] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu3[6] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu3[6] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu3[7] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu3[7] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu3[7] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu3[7] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu3[8] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu3[8] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu3[8] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu3[8] == `MESI_ISC_TB_CPU_MESI_I));
assume property (@(posedge clk) (cache_state_cpu3[9] == `MESI_ISC_TB_CPU_MESI_M) || (cache_state_cpu3[9] == `MESI_ISC_TB_CPU_MESI_E)
    || (cache_state_cpu3[9] == `MESI_ISC_TB_CPU_MESI_S) || (cache_state_cpu3[9] == `MESI_ISC_TB_CPU_MESI_I));

assert property (@(posedge clk) $fell(rst) |-> cache_state_cpu0[0] == `MESI_ISC_TB_CPU_MESI_I);
assert property (@(posedge clk) $fell(rst) |-> tb_ins_array[0] == `MESI_ISC_TB_INS_NOP);
assert property (@(posedge clk) $fell(rst) |-> tb_ins_array[1] == `MESI_ISC_TB_INS_NOP);
assert property (@(posedge clk) $fell(rst) |-> tb_ins_array[2] == `MESI_ISC_TB_INS_NOP);
assert property (@(posedge clk) $fell(rst) |-> tb_ins_array[3] == `MESI_ISC_TB_INS_NOP);

//assert propert (@(posedge clk) cbus_cmd3 == `MESI_ISC_CBUS_CMD_NOP 
assert property (@(posedge clk) cache_state_cpu3[0] == `MESI_ISC_TB_CPU_MESI_M |-> 
    (cache_state_cpu2[0] == `MESI_ISC_TB_CPU_MESI_I) && (cache_state_cpu1[0] == `MESI_ISC_TB_CPU_MESI_I)
    && (cache_state_cpu0[0] == `MESI_ISC_TB_CPU_MESI_I));

assert property (@(posedge clk) (mbus_cmd_array[3] == `MESI_ISC_MBUS_CMD_WR_BROAD) ##1 

endmodule


module Wrapper;


bind mesi_isc_tb top_props wrp_top (
    .clk(clk),
    .rst(rst),
    .cbus_addr    (cbus_addr),
    .cbus_cmd3    (cbus_cmd3),
    .cbus_cmd2    (cbus_cmd2),
    .cbus_cmd1    (cbus_cmd1),
    .cbus_cmd0    (cbus_cmd0),
    .mbus_data_rd    (mbus_data_rd),
    .mbus_ack     (mbus_ack),
    .tb_ins_array       (tb_ins_array),
    .tb_ins_addr3  (tb_ins_addr3),
    .tb_ins_addr2  (tb_ins_addr2),
    .tb_ins_addr1  (tb_ins_addr1),
    .tb_ins_addr0  (tb_ins_addr0),
    .mbus_cmd_array     (mbus_cmd_array),
    .mbus_addr_array    (mbus_addr_array),
    .mbus_data_wr_array    (mbus_data_wr_array),
    .cbus_ack3     (cbus_ack3),
    .cbus_ack2     (cbus_ack2),
    .cbus_ack1     (cbus_ack1),
    .cbus_ack0     (cbus_ack0),
    .tb_ins_ack   (tb_ins_ack),
    .cache_state_cpu0 (mesi_isc_tb_cpu0.cache_state),
    .cache_state_cpu1 (mesi_isc_tb_cpu1.cache_state),
    .cache_state_cpu2 (mesi_isc_tb_cpu2.cache_state),
    .cache_state_cpu3 (mesi_isc_tb_cpu3.cache_state)
);

endmodule
