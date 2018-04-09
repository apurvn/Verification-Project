module mesi_isc_props (
    input clk, rst
);

endmodule


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
assume property (@(posedge clk) status_empty_o |-> !rd_i);
assume property (@(posedge clk) status_full_o |-> !wr_i);

// Assume that the input data is known and stable when writing
// Assume that the output data is known and stable when reading a non-empty FIFO
assume property (@(posedge clk) disable iff(rst) wr_i |-> !$isunknown(data_i) && $stable(data_i));
assume property (@(posedge clk) disable iff(rst) rd_i && !status_empty_o|-> !$isunknown(data_o) && $stable(data_o));

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


endmodule


module breq_fifos_cntl_props (
    clk,
    rst,
    mbus_cmd_array_i,
    fifo_status_empty_array_i,
    fifo_status_full_array_i,
    broad_fifo_status_full_i,
    broad_addr_array_i,
    broad_type_array_i,
    broad_id_array_i,
    // Outputs
    mbus_ack_array_o,
    fifo_wr_array_o,
    fifo_rd_array_o,
    broad_fifo_wr_o,
    broad_addr_o,
    broad_type_o,
    broad_cpu_id_o,
    broad_id_o,
    breq_type_array_o,
    breq_cpu_id_array_o,
    breq_id_array_o
);

parameter
  MBUS_CMD_WIDTH           = 3,
  ADDR_WIDTH               = 32,
  BROAD_TYPE_WIDTH         = 2,  
  BROAD_ID_WIDTH           = 7;

input clk;
input rst;

input [4*MBUS_CMD_WIDTH-1:0] mbus_cmd_array_i;
input [3:0] fifo_status_empty_array_i;       
input [3:0] fifo_status_full_array_i;
input broad_fifo_status_full_i;
input [4*ADDR_WIDTH-1      :0] broad_addr_array_i;
input [4*BROAD_TYPE_WIDTH-1:0] broad_type_array_i;
input [4*BROAD_ID_WIDTH-1  :0] broad_id_array_i;
     
input [3:0]            mbus_ack_array_o;
input [3:0]            fifo_wr_array_o;
input [3:0]            fifo_rd_array_o; 
input                  broad_fifo_wr_o;
input [ADDR_WIDTH-1      :0] broad_addr_o;
input [BROAD_TYPE_WIDTH-1:0] broad_type_o;
input [1:0]                  broad_cpu_id_o;
input [BROAD_ID_WIDTH-1:  0] broad_id_o;
input [4*BROAD_TYPE_WIDTH-1:0] breq_type_array_o;
input [4*2-1:0]              breq_cpu_id_array_o;
input [4*BROAD_ID_WIDTH-1:0] breq_id_array_o;





endmodule


module Wrapper;

//bind mesi_isc mesi_isc_props wrp_mesi_isc (
//    .clk(clk),
//    .rst(rst)
//);

bind mesi_isc_basic_fifo mesi_isc_fifo_props wrp_mesi_isc_fifo (
    .clk(clk),
    .rst(rst),
    .wr_i(wr_i),
    .rd_i(rd_i),
    .data_i(data_i),
    .data_o(data_o),
    .status_empty_o(status_empty_o),
    .status_full_o(status_full_o),
    .ptr_wr(ptr_wr),
    .ptr_rd(ptr_rd),
    .fifo_depth(fifo_depth),
    .entry(entry)
);


//bind mesi_isc_breq_fifos_cntl breq_fifos_cntl_props  wrp_breq_cntl (
//    .clk(clk),
//    .rst(rst),
//    .mbus_cmd_array_i(mbus_cmd_array_i),
//    .fifo_status_empty_array_i(fifo_status_empty_array_i),
//    .fifo_status_full_array_i(fifo_status_full_array_i),
//    .broad_fifo_status_full_i(broad_fifo_status_full_i),
//    .broad_addr_array_i(broad_addr_array_i),
//    .broad_type_array_i(broad_type_array_i),
//    .broad_id_array_i(broad_id_array_i),
//    .mbus_ack_array_o(mbus_ack_array_o),
//    .fifo_wr_array_o(fifo_wr_array_o),
//    .fifo_rd_array_o(fifo_rd_array_o),
//    .broad_fifo_wr_o(broad_fifo_wr_o),
//    .broad_addr_o(broad_addr_o),
//    .broad_type_o(broad_type_o),
//    .broad_cpu_id_o(broad_cpu_id_o),
//    .broad_id_o(broad_id_o),
//    .breq_type_array_o(breq_type_array_o),
//    .breq_cpu_id_array_o(breq_cpu_id_array_o),
//    .breq_id_array_o(breq_id_array_o)
//);


endmodule
