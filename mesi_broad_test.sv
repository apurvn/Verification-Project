module broad_props (
     clk,
     rst,
     cbus_ack_array_i,
     broad_fifo_wr_i,
     broad_addr_i,
     broad_type_i,
     broad_cpu_id_i,
     broad_id_i,
     cbus_addr_o,
     cbus_cmd_array_o,
     fifo_status_full_o
);

parameter
  CBUS_CMD_WIDTH           = 3,
  ADDR_WIDTH               = 32,
  BROAD_TYPE_WIDTH         = 2,  
  BROAD_ID_WIDTH           = 5,  
  BROAD_REQ_FIFO_SIZE      = 4,
  BROAD_REQ_FIFO_SIZE_LOG2 = 2;
   
input clk; 
input rst; 
input [3:0] cbus_ack_array_i;
input broad_fifo_wr_i; 
input [ADDR_WIDTH-1:0] broad_addr_i; 
input [BROAD_TYPE_WIDTH-1:0] broad_type_i; 
input [1:0] broad_cpu_id_i; 
input [BROAD_ID_WIDTH-1:0] broad_id_i; 
input [ADDR_WIDTH-1:0] cbus_addr_o; 
input [4*CBUS_CMD_WIDTH-1:0] cbus_cmd_array_o; 
input fifo_status_full_o; 


endmodule   



module Wrapper;


bind mesi_isc_broad broad_props  wrp_broad (
     .clk(clk),
     .rst(rst),
     .cbus_ack_array_i(cbus_ack_array_i),
     .broad_fifo_wr_i(broad_fifo_wr_i),
     .broad_addr_i(broad_addr_i),
     .broad_type_i(broad_type_i),
     .broad_cpu_id_i(broad_cpu_id_i),
     .broad_id_i(broad_id_i),
     .cbus_addr_o(cbus_addr_o),
     .cbus_cmd_array_o(cbus_cmd_array_o),
     .fifo_status_full_o(fifo_status_full_o)
);


endmodule
