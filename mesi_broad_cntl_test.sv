module broad_cntl_props (
    clk,
    rst,
    cbus_ack_array_i,
    fifo_status_empty_i,
    fifo_status_full_i,
    broad_snoop_type_i,
    broad_snoop_cpu_id_i,
    broad_snoop_id_i,
    // Outputs
    cbus_cmd_array_o,
    broad_fifo_rd_o
);

parameter
  CBUS_CMD_WIDTH           = 3,
  BROAD_TYPE_WIDTH         = 2,
  BROAD_ID_WIDTH           = 5;
   
input clk;          
input rst;          
input [3:0] cbus_ack_array_i;
input fifo_status_empty_i;
input fifo_status_full_i;
input [BROAD_TYPE_WIDTH-1:0] broad_snoop_type_i; 
input [1:0]  broad_snoop_cpu_id_i; 
input [BROAD_ID_WIDTH-1:0] broad_snoop_id_i; 
output [4*CBUS_CMD_WIDTH-1:0] cbus_cmd_array_o; 
output broad_fifo_rd_o;

// Reset values
assert property (@(posedge clk) $fell(rst) |-> broad_fifo_rd_o == 0);



endmodule   



module Wrapper;


bind mesi_isc_broad_cntl broad_cntl_props  wrp_broad_cntl (
    .clk(clk),
    .rst(rst),
    .cbus_ack_array_i(cbus_ack_array_i),
    .fifo_status_empty_i(fifo_status_empty_i),
    .fifo_status_full_i(fifo_status_full_i),
    .broad_snoop_type_i(broad_snoop_type_i),
    .broad_snoop_cpu_id_i(broad_snoop_cpu_id_i),
    .broad_snoop_id_i(broad_snoop_id_i),
    .cbus_cmd_array_o(cbus_cmd_array_o),
    .broad_fifo_rd_o(broad_fifo_rd_o)
);


endmodule
