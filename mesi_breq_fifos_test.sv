module mesi_isc_fifo_props (
     // Inputs
     clk,
     rst,
     wr_i,
     rd_i,
     data_i,
     // Outputs
     data_o,
     status_empty_o,
     status_full_o,
     // Internal signals
     ptr_wr,
     ptr_rd,
     entry,
     fifo_depth
);

parameter
  DATA_WIDTH        = 32,
  FIFO_SIZE         = 4,
  FIFO_SIZE_LOG2    = 2;

input clk; 
input rst; 
input wr_i;
input rd_i; 
input [DATA_WIDTH-1:0] data_i; 
input [DATA_WIDTH-1:0] data_o; 
input status_empty_o;
input status_full_o;
input [FIFO_SIZE_LOG2-1:0] ptr_wr;
input [FIFO_SIZE_LOG2-1:0] ptr_rd;
input [DATA_WIDTH-1:0] entry [FIFO_SIZE-1:0];
input [FIFO_SIZE_LOG2-1:0] fifo_depth;

logic [1:0] ptr_wr_updt = ptr_wr + 2'b11;   //ptr_wr-1
logic [1:0] ptr_rd_updt = ptr_rd + 2'b11;   //ptr_rd-1 

// Shouldn't read when FIFO is empty and shouldn't write when it is full
//assume property (@(posedge clk) status_empty_o |-> !rd_i);
//assume property (@(posedge clk) status_full_o |-> !wr_i);

// Assume that the input data is known and stable when writing
// Assume that the output data is known and stable when reading a non-empty FIFO
//assume property (@(posedge clk) disable iff(rst) wr_i |-> !$isunknown(data_i) && $stable(data_i));
//assume property (@(posedge clk) disable iff(rst) rd_i && !status_empty_o|-> !$isunknown(data_o) && $stable(data_o));

// FIFO empty on reset and data_o is set to zero (rtl specs)
assert property (@(posedge clk) $fell(rst) |-> status_empty_o && !status_full_o);
assert property (@(posedge clk) $fell(rst) |-> !data_o);

// FIFO empty when ptr_wr-ptr_rd=1 and reading from FIFO
assert property (@(posedge clk) disable iff(rst) (fifo_depth==1) && rd_i && !wr_i |=> status_empty_o);

// FIFO full when ptr_wr-ptr_rd=FIFO_SIZE-1 and writing to FIFO
assert property (@(posedge clk) disable iff(rst) (fifo_depth==FIFO_SIZE-1) && !rd_i && wr_i |=> status_full_o);

// FIFO depth 0 means either FIFO is full or FIFO is empty
assert property (@(posedge clk) disable iff(rst) (fifo_depth==0) |-> status_full_o | status_empty_o);

// Write and read pointers are updated on write and read respectively
assert property (@(posedge clk) disable iff(rst) wr_i |=> ptr_wr_updt==$past(ptr_wr,1));
assert property (@(posedge clk) disable iff(rst) rd_i |=> ptr_rd_updt==$past(ptr_rd,1));

// Empty and full signals should never be active at the same time
assert property (@(posedge clk) disable iff(rst) !(status_empty_o && status_full_o));

// Cannot read and write from the same location at the same time
assert property (@(posedge clk) disable iff(rst) !(rd_i && wr_i && (ptr_wr==ptr_rd)));

// FIFO gets full and FIFO gets empty
cover property (@(posedge clk) $rose(status_full_o));
cover property (@(posedge clk) $rose(status_empty_o));

// Read and write operation occurs atleast once
cover property (@(posedge clk) wr_i);
cover property (@(posedge clk) rd_i);
cover property (@(posedge clk) wr_i & rd_i);

endmodule


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

cover property (@(posedge clk) fifo_status_full_array[3]);
cover property (@(posedge clk) fifo_status_full_array[2]);
cover property (@(posedge clk) fifo_status_full_array[1]);
cover property (@(posedge clk) fifo_status_full_array[0]);

cover property (@(posedge clk) fifo_status_empty_array[3]);
cover property (@(posedge clk) fifo_status_empty_array[2]);
cover property (@(posedge clk) fifo_status_empty_array[1]);
cover property (@(posedge clk) fifo_status_empty_array[0]);

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

bind mesi_isc_breq_fifos mesi_isc_fifo_props wrp_mesi_isc_fifo3 (
    .clk(fifo_3.clk),
    .rst(fifo_3.rst),
    .wr_i(fifo_3.wr_i),
    .rd_i(fifo_3.rd_i),
    .data_i(fifo_3.data_i),
    .data_o(fifo_3.data_o),
    .status_empty_o(fifo_3.status_empty_o),
    .status_full_o(fifo_3.status_full_o),
    .ptr_wr(fifo_3.ptr_wr),
    .ptr_rd(fifo_3.ptr_rd),
    .fifo_depth(fifo_3.fifo_depth),
    .entry(fifo_3.entry)
);

//bind mesi_isc_breq_fifos mesi_isc_fifo_props wrp_mesi_isc_fifo2 (
//    .clk(fifo_2.clk),
//    .rst(fifo_2.rst),
//    .wr_i(fifo_2.wr_i),
//    .rd_i(fifo_2.rd_i),
//    .data_i(fifo_2.data_i),
//    .data_o(fifo_2.data_o),
//    .status_empty_o(fifo_2.status_empty_o),
//    .status_full_o(fifo_2.status_full_o),
//    .ptr_wr(fifo_2.ptr_wr),
//    .ptr_rd(fifo_2.ptr_rd),
//    .fifo_depth(fifo_2.fifo_depth),
//    .entry(fifo_2.entry)
//);
//
//bind mesi_isc_breq_fifos mesi_isc_fifo_props wrp_mesi_isc_fifo1 (
//    .clk(fifo_1.clk),
//    .rst(fifo_1.rst),
//    .wr_i(fifo_1.wr_i),
//    .rd_i(fifo_1.rd_i),
//    .data_i(fifo_1.data_i),
//    .data_o(fifo_1.data_o),
//    .status_empty_o(fifo_1.status_empty_o),
//    .status_full_o(fifo_1.status_full_o),
//    .ptr_wr(fifo_1.ptr_wr),
//    .ptr_rd(fifo_1.ptr_rd),
//    .fifo_depth(fifo_1.fifo_depth),
//    .entry(fifo_1.entry)
//);
//
//bind mesi_isc_breq_fifos mesi_isc_fifo_props wrp_mesi_isc_fifo0 (
//    .clk(fifo_0.clk),
//    .rst(fifo_0.rst),
//    .wr_i(fifo_0.wr_i),
//    .rd_i(fifo_0.rd_i),
//    .data_i(fifo_0.data_i),
//    .data_o(fifo_0.data_o),
//    .status_empty_o(fifo_0.status_empty_o),
//    .status_full_o(fifo_0.status_full_o),
//    .ptr_wr(fifo_0.ptr_wr),
//    .ptr_rd(fifo_0.ptr_rd),
//    .fifo_depth(fifo_0.fifo_depth),
//    .entry(fifo_0.entry)
//);

endmodule
