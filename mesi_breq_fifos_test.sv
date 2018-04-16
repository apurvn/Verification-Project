module breq_fifos_props (
     clk,
     rst,
     mbus_cmd_array_i,
     mbus_addr_array_i,
     broad_fifo_status_full_i,
     mbus_ack_array_o,
     broad_fifo_wr_o,
     broad_addr_o,
     broad_type_o,
     broad_cpu_id_o,
     broad_id_o,
     fifo_wr_array,
     fifo_rd_array,
     fifo_status_empty_array,
     fifo_status_full_array
);
   
parameter
  MBUS_CMD_WIDTH           = 3,
  ADDR_WIDTH               = 32,
  BROAD_TYPE_WIDTH         = 2,  
  BROAD_ID_WIDTH           = 7,  
  BREQ_FIFO_SIZE           = 2,
  BREQ_FIFO_SIZE_LOG2      = 1;
   
input clk; 
input rst; 
input [4*MBUS_CMD_WIDTH-1:0] mbus_cmd_array_i; 
input [4*ADDR_WIDTH-1:0] mbus_addr_array_i; 
input broad_fifo_status_full_i; 
input [3:0] mbus_ack_array_o; 
input broad_fifo_wr_o; 
input [ADDR_WIDTH-1:0] broad_addr_o; 
input [BROAD_TYPE_WIDTH-1:0] broad_type_o; 
input [1:0] broad_cpu_id_o; 
input [BROAD_ID_WIDTH-1:0] broad_id_o; 
input [3:0] fifo_wr_array;
input [3:0] fifo_rd_array;
input [3:0] fifo_status_empty_array;
input [3:0] fifo_status_full_array;

logic [MBUS_CMD_WIDTH-1:0] mbus_cmd_array_i_3 = mbus_cmd_array_i[(3+1)*MBUS_CMD_WIDTH-1 : 3*MBUS_CMD_WIDTH];
logic [MBUS_CMD_WIDTH-1:0] mbus_cmd_array_i_2 = mbus_cmd_array_i[(2+1)*MBUS_CMD_WIDTH-1 : 2*MBUS_CMD_WIDTH];
logic [MBUS_CMD_WIDTH-1:0] mbus_cmd_array_i_1 = mbus_cmd_array_i[(1+1)*MBUS_CMD_WIDTH-1 : 1*MBUS_CMD_WIDTH];
logic [MBUS_CMD_WIDTH-1:0] mbus_cmd_array_i_0 = mbus_cmd_array_i[(0+1)*MBUS_CMD_WIDTH-1 : 0*MBUS_CMD_WIDTH];

assume property (@(posedge clk) broad_type_o != 3);

assume property (@(posedge clk) mbus_cmd_array_i_3 != 5);
assume property (@(posedge clk) mbus_cmd_array_i_3 != 6);
assume property (@(posedge clk) mbus_cmd_array_i_3 != 7);

assume property (@(posedge clk) mbus_cmd_array_i_2 != 5);
assume property (@(posedge clk) mbus_cmd_array_i_2 != 6);
assume property (@(posedge clk) mbus_cmd_array_i_2 != 7);

assume property (@(posedge clk) mbus_cmd_array_i_1 != 5);
assume property (@(posedge clk) mbus_cmd_array_i_1 != 6);
assume property (@(posedge clk) mbus_cmd_array_i_1 != 7);

assume property (@(posedge clk) mbus_cmd_array_i_0 != 5);
assume property (@(posedge clk) mbus_cmd_array_i_0 != 6);
assume property (@(posedge clk) mbus_cmd_array_i_0 != 7);

assert property (@(posedge clk) fifo_status_empty_array[0] |-> !fifo_rd_array[0]);
assert property (@(posedge clk) fifo_status_empty_array[1] |-> !fifo_rd_array[1]);
assert property (@(posedge clk) fifo_status_empty_array[2] |-> !fifo_rd_array[2]);
assert property (@(posedge clk) fifo_status_empty_array[3] |-> !fifo_rd_array[3]);

assert property (@(posedge clk) fifo_status_full_array[3] |-> !fifo_wr_array[3]);
assert property (@(posedge clk) fifo_status_full_array[2] |-> !fifo_wr_array[2]);
assert property (@(posedge clk) fifo_status_full_array[1] |-> !fifo_wr_array[1]);
assert property (@(posedge clk) fifo_status_full_array[0] |-> !fifo_wr_array[0]);

endmodule   


module Wrapper;


bind mesi_isc_breq_fifos breq_fifos_props  wrp_breq (
    .clk(clk),
    .rst(rst),
    .mbus_cmd_array_i(mbus_cmd_array_i),
    .mbus_addr_array_i(mbus_addr_array_i),
    .broad_fifo_status_full_i(broad_fifo_status_full_i),
    .mbus_ack_array_o(mbus_ack_array_o),
    .broad_fifo_wr_o(broad_fifo_wr_o),
    .broad_addr_o(broad_addr_o),
    .broad_type_o(broad_type_o),
    .broad_cpu_id_o(broad_cpu_id_o),
    .broad_id_o(broad_id_o),
    .fifo_wr_array(fifo_wr_array),
    .fifo_rd_array(fifo_rd_array),
    .fifo_status_empty_array(fifo_status_empty_array),
    .fifo_status_full_array(fifo_status_full_array)
);


endmodule
