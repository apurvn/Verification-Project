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
input [4*CBUS_CMD_WIDTH-1:0] cbus_cmd_array_o; 
input broad_fifo_rd_o;

logic cbus_cmd3 = cbus_cmd_array_o[(3+1)*CBUS_CMD_WIDTH-1 : 3*CBUS_CMD_WIDTH];
logic cbus_cmd2 = cbus_cmd_array_o[(2+1)*CBUS_CMD_WIDTH-1 : 2*CBUS_CMD_WIDTH];
logic cbus_cmd1 = cbus_cmd_array_o[(1+1)*CBUS_CMD_WIDTH-1 : 1*CBUS_CMD_WIDTH];
logic cbus_cmd0 = cbus_cmd_array_o[(0+1)*CBUS_CMD_WIDTH-1 : 0*CBUS_CMD_WIDTH];

// Assume properties
assume property (@(posedge clk) cbus_cmd3 != 3'd5);
assume property (@(posedge clk) cbus_cmd3 != 3'd6);
assume property (@(posedge clk) cbus_cmd3 != 3'd7);

assert property (@(posedge clk) cbus

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
