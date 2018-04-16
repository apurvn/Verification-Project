module cpu_props (
     // Inputs
     clk,
     rst,
     cbus_addr_i,
     cbus_cmd_i,
     mbus_data_i,
     mbus_ack_i,
     cpu_id_i,
     tb_ins_i,
     tb_ins_addr_i,
     // Outputs
     mbus_cmd_o,
     mbus_addr_o,
     mbus_data_o,
     cbus_ack_o,
     tb_ins_ack_o,
     m_state, 
     c_state,
     cache_state0,
     cache_state1,
     cache_state2,
     cache_state3,
     cache_state4,
     cache_state5,
     cache_state6,
     cache_state7,
     cache_state8,
     cache_state9
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
input [ADDR_WIDTH-1:0] cbus_addr_i; 
input [CBUS_CMD_WIDTH-1:0] cbus_cmd_i; 
input [DATA_WIDTH-1:0] mbus_data_i; 
input mbus_ack_i; 
input [1:0] cpu_id_i;
input [3:0] tb_ins_i; 
input [3:0] tb_ins_addr_i; 
input [MBUS_CMD_WIDTH-1:0] mbus_cmd_o; 
input [ADDR_WIDTH-1:0] mbus_addr_o; 
input [DATA_WIDTH-1:0] mbus_data_o; 
input cbus_ack_o; 
input tb_ins_ack_o; 
input m_state, c_state;
input [3:0] cache_state0;
input [3:0] cache_state1;
input [3:0] cache_state2;
input [3:0] cache_state3;
input [3:0] cache_state4;
input [3:0] cache_state5;
input [3:0] cache_state6;
input [3:0] cache_state7;
input [3:0] cache_state8;
input [3:0] cache_state9;


assert property (@(posedge clk) $fell(rst) |-> m_state==`MESI_ISC_TB_CPU_M_STATE_IDLE); 
assert property (@(posedge clk) $fell(rst) |-> c_state==`MESI_ISC_TB_CPU_C_STATE_IDLE); 



endmodule


module Wrapper;


bind mesi_isc_tb_cpu cpu_props wrp_cpu (
    .clk(clk),
    .rst(rst),
    .cbus_addr_i(cbus_addr_i),
    .cbus_cmd_i(cbus_cmd_i),
    .mbus_data_i(mbus_data_i),
    .mbus_ack_i(mbus_ack_i),
    .cpu_id_i(cpu_id_i),
    .tb_ins_i(tb_ins_i),
    .tb_ins_addr_i(tb_ins_addr_i),
    .mbus_cmd_o(mbus_cmd_o),
    .mbus_addr_o(mbus_addr_o),
    .mbus_data_o(mbus_data_o),
    .cbus_ack_o(cbus_ack_o),
    .tb_ins_ack_o(tb_ins_ack_o),
    .m_state(m_state),
    .c_state(c_state)
    .cache_state0(cache_state0),
    .cache_state1(cache_state1),
    .cache_state2(cache_state2),
    .cache_state3(cache_state3),
    .cache_state4(cache_state4),
    .cache_state5(cache_state5),
    .cache_state6(cache_state6),
    .cache_state7(cache_state7),
    .cache_state8(cache_state8),
    .cache_state9(cache_state9)
);

endmodule
