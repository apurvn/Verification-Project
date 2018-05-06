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

assume property (@(posedge clk) (broad_snoop_type_i == `MESI_ISC_BREQ_TYPE_RD) || (broad_snoop_type_i == `MESI_ISC_BREQ_TYPE_WR) || (broad_snoop_type_i == `MESI_ISC_BREQ_TYPE_NOP));
assume property (@(posedge clk) (cbus_active_broad_array == 4'b0000) || (cbus_active_broad_array == 4'b1110) || (cbus_active_broad_array == 4'b1101) ||
        (cbus_active_broad_array == 4'b1011) || (cbus_active_broad_array == 4'b0111) );
assume property (@(posedge clk) (cbus_active_en_access_array == 4'b0000) || (cbus_active_en_access_array == 4'b0001) || (cbus_active_en_access_array == 4'b0010) ||
        (cbus_active_en_access_array == 4'b0100) || (cbus_active_en_access_array == 4'b1000) );

// Reset values
assert property (@(posedge clk) $fell(rst) |-> broad_fifo_rd_o == 0);
assert property (@(posedge clk) $fell(rst) |-> cbus_active_broad_array == 0);
assert property (@(posedge clk) $fell(rst) |-> cbus_active_en_access_array == 0);
assert property (@(posedge clk) $fell(rst) |-> broadcast_in_progress == 0);

// Cbus commands
assert property (@(posedge clk) disable iff(rst) cbus_active_broad_array[3] && (broad_snoop_type_i==`MESI_ISC_BREQ_TYPE_WR) |-> cbus_cmd3 == `MESI_ISC_CBUS_CMD_WR_SNOOP);
assert property (@(posedge clk) disable iff(rst) cbus_active_broad_array[3] && (broad_snoop_type_i==`MESI_ISC_BREQ_TYPE_RD) |-> cbus_cmd3 == `MESI_ISC_CBUS_CMD_RD_SNOOP);
assert property (@(posedge clk) disable iff(rst) !cbus_active_broad_array[3] && !(|cbus_active_broad_array) && cbus_active_en_access_array[3] && !broad_fifo_rd_o && (broad_snoop_type_i==`MESI_ISC_BREQ_TYPE_WR) |-> cbus_cmd3 == `MESI_ISC_CBUS_CMD_EN_WR);
assert property (@(posedge clk) disable iff(rst) !cbus_active_broad_array[3] && !(|cbus_active_broad_array) && cbus_active_en_access_array[3] && !broad_fifo_rd_o && (broad_snoop_type_i==`MESI_ISC_BREQ_TYPE_RD) |-> cbus_cmd3 == `MESI_ISC_CBUS_CMD_EN_RD);

assert property (@(posedge clk) disable iff(rst) cbus_active_broad_array[2] && (broad_snoop_type_i==`MESI_ISC_BREQ_TYPE_WR) |-> cbus_cmd2 == `MESI_ISC_CBUS_CMD_WR_SNOOP);
assert property (@(posedge clk) disable iff(rst) cbus_active_broad_array[2] && (broad_snoop_type_i==`MESI_ISC_BREQ_TYPE_RD) |-> cbus_cmd2 == `MESI_ISC_CBUS_CMD_RD_SNOOP);
assert property (@(posedge clk) disable iff(rst) !cbus_active_broad_array[2] && !(|cbus_active_broad_array) && cbus_active_en_access_array[2] && !broad_fifo_rd_o && (broad_snoop_type_i==`MESI_ISC_BREQ_TYPE_WR) |-> cbus_cmd2 == `MESI_ISC_CBUS_CMD_EN_WR);
assert property (@(posedge clk) disable iff(rst) !cbus_active_broad_array[2] && !(|cbus_active_broad_array) && cbus_active_en_access_array[2] && !broad_fifo_rd_o && (broad_snoop_type_i==`MESI_ISC_BREQ_TYPE_RD) |-> cbus_cmd2 == `MESI_ISC_CBUS_CMD_EN_RD);

assert property (@(posedge clk) disable iff(rst) cbus_active_broad_array[1] && (broad_snoop_type_i==`MESI_ISC_BREQ_TYPE_WR) |-> cbus_cmd1 == `MESI_ISC_CBUS_CMD_WR_SNOOP);
assert property (@(posedge clk) disable iff(rst) cbus_active_broad_array[1] && (broad_snoop_type_i==`MESI_ISC_BREQ_TYPE_RD) |-> cbus_cmd1 == `MESI_ISC_CBUS_CMD_RD_SNOOP);
assert property (@(posedge clk) disable iff(rst) !cbus_active_broad_array[1] && !(|cbus_active_broad_array) && cbus_active_en_access_array[1] && !broad_fifo_rd_o && (broad_snoop_type_i==`MESI_ISC_BREQ_TYPE_WR) |-> cbus_cmd1 == `MESI_ISC_CBUS_CMD_EN_WR);
assert property (@(posedge clk) disable iff(rst) !cbus_active_broad_array[1] && !(|cbus_active_broad_array) && cbus_active_en_access_array[1] && !broad_fifo_rd_o && (broad_snoop_type_i==`MESI_ISC_BREQ_TYPE_RD) |-> cbus_cmd1 == `MESI_ISC_CBUS_CMD_EN_RD);

assert property (@(posedge clk) disable iff(rst) cbus_active_broad_array[0] && (broad_snoop_type_i==`MESI_ISC_BREQ_TYPE_WR) |-> cbus_cmd0 == `MESI_ISC_CBUS_CMD_WR_SNOOP);
assert property (@(posedge clk) disable iff(rst) cbus_active_broad_array[0] && (broad_snoop_type_i==`MESI_ISC_BREQ_TYPE_RD) |-> cbus_cmd0 == `MESI_ISC_CBUS_CMD_RD_SNOOP);
assert property (@(posedge clk) disable iff(rst) !cbus_active_broad_array[0] && !(|cbus_active_broad_array) && cbus_active_en_access_array[0] && !broad_fifo_rd_o && (broad_snoop_type_i==`MESI_ISC_BREQ_TYPE_WR) |-> cbus_cmd0 == `MESI_ISC_CBUS_CMD_EN_WR);
assert property (@(posedge clk) disable iff(rst) !cbus_active_broad_array[0] && !(|cbus_active_broad_array) && cbus_active_en_access_array[0] && !broad_fifo_rd_o && (broad_snoop_type_i==`MESI_ISC_BREQ_TYPE_RD) |-> cbus_cmd0 == `MESI_ISC_CBUS_CMD_EN_RD);

assert property (@(posedge clk) disable iff(rst) !broadcast_in_progress && !broad_fifo_rd_o && !fifo_status_empty_i |=> broadcast_in_progress);
assert property (@(posedge clk) disable iff(rst) !broadcast_in_progress && !broad_fifo_rd_o && !fifo_status_empty_i && (broad_snoop_cpu_id_i==0) |=> cbus_active_broad_array==4'b1110);
assert property (@(posedge clk) disable iff(rst) !broadcast_in_progress && !broad_fifo_rd_o && !fifo_status_empty_i && (broad_snoop_cpu_id_i==0) |=> cbus_active_en_access_array==4'b0001);

assert property (@(posedge clk) disable iff(rst) !broadcast_in_progress && !broad_fifo_rd_o && !fifo_status_empty_i && (broad_snoop_cpu_id_i==1) |=> cbus_active_broad_array==4'b1101);
assert property (@(posedge clk) disable iff(rst) !broadcast_in_progress && !broad_fifo_rd_o && !fifo_status_empty_i && (broad_snoop_cpu_id_i==1) |=> cbus_active_en_access_array==4'b0010);

assert property (@(posedge clk) disable iff(rst) !broadcast_in_progress && !broad_fifo_rd_o && !fifo_status_empty_i && (broad_snoop_cpu_id_i==2) |=> cbus_active_broad_array==4'b1011);
assert property (@(posedge clk) disable iff(rst) !broadcast_in_progress && !broad_fifo_rd_o && !fifo_status_empty_i && (broad_snoop_cpu_id_i==2) |=> cbus_active_en_access_array==4'b0100);

assert property (@(posedge clk) disable iff(rst) !broadcast_in_progress && !broad_fifo_rd_o && !fifo_status_empty_i && (broad_snoop_cpu_id_i==3) |=> cbus_active_broad_array==4'b0111);
assert property (@(posedge clk) disable iff(rst) !broadcast_in_progress && !broad_fifo_rd_o && !fifo_status_empty_i && (broad_snoop_cpu_id_i==3) |=> cbus_active_en_access_array==4'b1000);

assert property (@(posedge clk) disable iff(rst) !broadcast_in_progress && !broad_fifo_rd_o && !fifo_status_empty_i && (broad_snoop_cpu_id_i==0) |=> !broad_fifo_rd_o);

// Cover porperties 
cover property (@(posedge clk) broad_fifo_rd_o);
cover property (@(posedge clk) fifo_status_empty_i);
cover property (@(posedge clk) fifo_status_full_i);

cover property (@(posedge clk) broad_snoop_id_i == 0);
cover property (@(posedge clk) broad_snoop_id_i == 1);
cover property (@(posedge clk) broad_snoop_id_i == 2);
cover property (@(posedge clk) broad_snoop_id_i == 3);

cover property (@(posedge clk) cbus_cmd3==`MESI_ISC_CBUS_CMD_RD_SNOOP);
cover property (@(posedge clk) cbus_cmd3==`MESI_ISC_CBUS_CMD_WR_SNOOP);
cover property (@(posedge clk) cbus_cmd3==`MESI_ISC_CBUS_CMD_EN_WR);
cover property (@(posedge clk) cbus_cmd3==`MESI_ISC_CBUS_CMD_EN_RD);

cover property (@(posedge clk) cbus_cmd2==`MESI_ISC_CBUS_CMD_RD_SNOOP);
cover property (@(posedge clk) cbus_cmd2==`MESI_ISC_CBUS_CMD_WR_SNOOP);
cover property (@(posedge clk) cbus_cmd2==`MESI_ISC_CBUS_CMD_EN_WR);
cover property (@(posedge clk) cbus_cmd2==`MESI_ISC_CBUS_CMD_EN_RD);

cover property (@(posedge clk) cbus_cmd1==`MESI_ISC_CBUS_CMD_RD_SNOOP);
cover property (@(posedge clk) cbus_cmd1==`MESI_ISC_CBUS_CMD_WR_SNOOP);
cover property (@(posedge clk) cbus_cmd1==`MESI_ISC_CBUS_CMD_EN_WR);
cover property (@(posedge clk) cbus_cmd1==`MESI_ISC_CBUS_CMD_EN_RD);

cover property (@(posedge clk) cbus_cmd0==`MESI_ISC_CBUS_CMD_RD_SNOOP);
cover property (@(posedge clk) cbus_cmd0==`MESI_ISC_CBUS_CMD_WR_SNOOP);
cover property (@(posedge clk) cbus_cmd0==`MESI_ISC_CBUS_CMD_EN_WR);
cover property (@(posedge clk) cbus_cmd0==`MESI_ISC_CBUS_CMD_EN_RD);



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
