module mesi_isc_props (
     clk,
     rst,
     mbus_cmd3_i,
     mbus_cmd2_i,
     mbus_cmd1_i,
     mbus_cmd0_i,
     mbus_addr3_i,
     mbus_addr2_i,
     mbus_addr1_i,
     mbus_addr0_i,
     cbus_ack3_i,
     cbus_ack2_i,
     cbus_ack1_i,
     cbus_ack0_i,
     cbus_addr_o,
     cbus_cmd3_o,
     cbus_cmd2_o,
     cbus_cmd1_o,
     cbus_cmd0_o,
     mbus_ack3_o,
     mbus_ack2_o,
     mbus_ack1_o,
     mbus_ack0_o,
     broad_fifo_status_full,
     fifo_status_empty_array
);

parameter
  CBUS_CMD_WIDTH           = 3,
  ADDR_WIDTH               = 32,
  BROAD_TYPE_WIDTH         = 2,
  BROAD_ID_WIDTH           = 5,  
  BROAD_REQ_FIFO_SIZE      = 4,
  BROAD_REQ_FIFO_SIZE_LOG2 = 2,
  MBUS_CMD_WIDTH           = 3,
  BREQ_FIFO_SIZE           = 2,
  BREQ_FIFO_SIZE_LOG2      = 1;
   
// System
input                   clk;          // System clock
input                   rst;          // Active high system reset
// Main buses
input [MBUS_CMD_WIDTH-1:0] mbus_cmd3_i; // Main bus3 command
input [MBUS_CMD_WIDTH-1:0] mbus_cmd2_i; // Main bus2 command
input [MBUS_CMD_WIDTH-1:0] mbus_cmd1_i; // Main bus1 command
input [MBUS_CMD_WIDTH-1:0] mbus_cmd0_i; // Main bus0 command
// Coherence buses
input [ADDR_WIDTH-1:0]  mbus_addr3_i;  // Coherence bus3 address
input [ADDR_WIDTH-1:0]  mbus_addr2_i;  // Coherence bus2 address
input [ADDR_WIDTH-1:0]  mbus_addr1_i;  // Coherence bus1 address
input [ADDR_WIDTH-1:0]  mbus_addr0_i;  // Coherence bus0 address
input cbus_ack3_i;  // Coherence bus3 acknowledge
input cbus_ack2_i;  // Coherence bus2 acknowledge
input cbus_ack1_i;  // Coherence bus1 acknowledge
input cbus_ack0_i;  // Coherence bus0 acknowledge
input broad_fifo_status_full;
input [3:0] fifo_status_empty_array;
   
// Outputs
//================================

input [ADDR_WIDTH-1:0] cbus_addr_o;  // Coherence bus address. All busses have
                                      // the same address
input [CBUS_CMD_WIDTH-1:0] cbus_cmd3_o; // Coherence bus3 command
input [CBUS_CMD_WIDTH-1:0] cbus_cmd2_o; // Coherence bus2 command
input [CBUS_CMD_WIDTH-1:0] cbus_cmd1_o; // Coherence bus1 command
input [CBUS_CMD_WIDTH-1:0] cbus_cmd0_o; // Coherence bus0 command


input mbus_ack3_o;  // Main bus3 acknowledge
input mbus_ack2_o;  // Main bus2 acknowledge
input mbus_ack1_o;  // Main bus1 acknowledge
input mbus_ack0_o;  // Main bus0 acknowledge

//assume property (@(posedge clk) 

// Properties for checking the acknowledge signals
assert property (@(posedge clk) disable iff(rst | broad_fifo_status_full | fifo_status_empty_array[3]) 
        mbus_cmd3_i== `MESI_ISC_MBUS_CMD_WR_BROAD |-> ##[1:4] mbus_ack3_o);
assert property (@(posedge clk) disable iff(rst | broad_fifo_status_full | fifo_status_empty_array[2]) 
        mbus_cmd2_i== `MESI_ISC_MBUS_CMD_WR_BROAD |-> ##[1:4] mbus_ack2_o);
assert property (@(posedge clk) disable iff(rst | broad_fifo_status_full | fifo_status_empty_array[1]) 
        mbus_cmd1_i== `MESI_ISC_MBUS_CMD_WR_BROAD |-> ##[1:4] mbus_ack1_o);
assert property (@(posedge clk) disable iff(rst | broad_fifo_status_full | fifo_status_empty_array[0]) 
        mbus_cmd0_i== `MESI_ISC_MBUS_CMD_WR_BROAD |-> ##[1:4] mbus_ack0_o);

// Properties for checking the braodcast signals 
assert property (@(posedge clk) disable iff(rst | broad_fifo_status_full | fifo_status_empty_array[3]) 
        mbus_cmd3_i== `MESI_ISC_MBUS_CMD_WR_BROAD |-> ##[1:4] cbus_cmd3_o == `MESI_ISC_CBUS_CMD_WR_SNOOP || cbus_cmd3_o == `MESI_ISC_CBUS_CMD_EN_WR);
assert property (@(posedge clk) disable iff(rst | broad_fifo_status_full | fifo_status_empty_array[3]) 
        mbus_cmd3_i== `MESI_ISC_MBUS_CMD_RD_BROAD |-> ##[1:4] cbus_cmd3_o == `MESI_ISC_CBUS_CMD_RD_SNOOP || cbus_cmd3_o == `MESI_ISC_CBUS_CMD_EN_RD);

assert property (@(posedge clk) disable iff(rst | broad_fifo_status_full | fifo_status_empty_array[2]) 
        mbus_cmd2_i== `MESI_ISC_MBUS_CMD_WR_BROAD |-> ##[1:4] cbus_cmd2_o == `MESI_ISC_CBUS_CMD_WR_SNOOP || cbus_cmd2_o == `MESI_ISC_CBUS_CMD_EN_WR);
assert property (@(posedge clk) disable iff(rst | broad_fifo_status_full | fifo_status_empty_array[2]) 
        mbus_cmd2_i== `MESI_ISC_MBUS_CMD_RD_BROAD |-> ##[1:4] cbus_cmd2_o == `MESI_ISC_CBUS_CMD_RD_SNOOP || cbus_cmd2_o == `MESI_ISC_CBUS_CMD_EN_RD);

assert property (@(posedge clk) disable iff(rst | broad_fifo_status_full | fifo_status_empty_array[1]) 
        mbus_cmd1_i== `MESI_ISC_MBUS_CMD_WR_BROAD |-> ##[1:4] cbus_cmd1_o == `MESI_ISC_CBUS_CMD_WR_SNOOP || cbus_cmd1_o == `MESI_ISC_CBUS_CMD_EN_WR);
assert property (@(posedge clk) disable iff(rst | broad_fifo_status_full | fifo_status_empty_array[1]) 
        mbus_cmd1_i== `MESI_ISC_MBUS_CMD_RD_BROAD |-> ##[1:4] cbus_cmd1_o == `MESI_ISC_CBUS_CMD_RD_SNOOP || cbus_cmd1_o == `MESI_ISC_CBUS_CMD_EN_RD);

assert property (@(posedge clk) disable iff(rst | broad_fifo_status_full | fifo_status_empty_array[0]) 
        mbus_cmd0_i== `MESI_ISC_MBUS_CMD_WR_BROAD |-> ##[1:4] cbus_cmd0_o == `MESI_ISC_CBUS_CMD_WR_SNOOP || cbus_cmd0_o == `MESI_ISC_CBUS_CMD_EN_WR);
assert property (@(posedge clk) disable iff(rst | broad_fifo_status_full | fifo_status_empty_array[0]) 
        mbus_cmd0_i== `MESI_ISC_MBUS_CMD_RD_BROAD |-> ##[1:4] cbus_cmd0_o == `MESI_ISC_CBUS_CMD_RD_SNOOP || cbus_cmd0_o == `MESI_ISC_CBUS_CMD_EN_RD);


// Cover properties for checking cache requests, broadcast requests, acknowledge and enables
cover property (@(posedge clk) mbus_cmd3_i==`MESI_ISC_MBUS_CMD_NOP);
cover property (@(posedge clk) mbus_cmd3_i==`MESI_ISC_MBUS_CMD_WR);
cover property (@(posedge clk) mbus_cmd3_i==`MESI_ISC_MBUS_CMD_RD);
cover property (@(posedge clk) mbus_cmd3_i==`MESI_ISC_MBUS_CMD_WR_BROAD);
cover property (@(posedge clk) mbus_cmd3_i==`MESI_ISC_MBUS_CMD_RD_BROAD);

cover property (@(posedge clk) mbus_cmd2_i==`MESI_ISC_MBUS_CMD_NOP);
cover property (@(posedge clk) mbus_cmd2_i==`MESI_ISC_MBUS_CMD_WR);
cover property (@(posedge clk) mbus_cmd2_i==`MESI_ISC_MBUS_CMD_RD);
cover property (@(posedge clk) mbus_cmd2_i==`MESI_ISC_MBUS_CMD_WR_BROAD);
cover property (@(posedge clk) mbus_cmd2_i==`MESI_ISC_MBUS_CMD_RD_BROAD);

cover property (@(posedge clk) mbus_cmd1_i==`MESI_ISC_MBUS_CMD_NOP);
cover property (@(posedge clk) mbus_cmd1_i==`MESI_ISC_MBUS_CMD_WR);
cover property (@(posedge clk) mbus_cmd1_i==`MESI_ISC_MBUS_CMD_RD);
cover property (@(posedge clk) mbus_cmd1_i==`MESI_ISC_MBUS_CMD_WR_BROAD);
cover property (@(posedge clk) mbus_cmd1_i==`MESI_ISC_MBUS_CMD_RD_BROAD);

cover property (@(posedge clk) mbus_cmd0_i==`MESI_ISC_MBUS_CMD_NOP);
cover property (@(posedge clk) mbus_cmd0_i==`MESI_ISC_MBUS_CMD_WR);
cover property (@(posedge clk) mbus_cmd0_i==`MESI_ISC_MBUS_CMD_RD);
cover property (@(posedge clk) mbus_cmd0_i==`MESI_ISC_MBUS_CMD_WR_BROAD);
cover property (@(posedge clk) mbus_cmd0_i==`MESI_ISC_MBUS_CMD_RD_BROAD);

cover property (@(posedge clk) cbus_ack3_i);
cover property (@(posedge clk) cbus_ack2_i);
cover property (@(posedge clk) cbus_ack1_i);
cover property (@(posedge clk) cbus_ack0_i);

cover property (@(posedge clk) mbus_ack3_o);
cover property (@(posedge clk) mbus_ack2_o);
cover property (@(posedge clk) mbus_ack1_o);
cover property (@(posedge clk) mbus_ack0_o);

cover property (@(posedge clk) cbus_cmd3_o==`MESI_ISC_CBUS_CMD_NOP);
cover property (@(posedge clk) cbus_cmd3_o==`MESI_ISC_CBUS_CMD_WR_SNOOP);
cover property (@(posedge clk) cbus_cmd3_o==`MESI_ISC_CBUS_CMD_RD_SNOOP);
cover property (@(posedge clk) cbus_cmd3_o==`MESI_ISC_CBUS_CMD_EN_WR);
cover property (@(posedge clk) cbus_cmd3_o==`MESI_ISC_CBUS_CMD_EN_RD);

cover property (@(posedge clk) cbus_cmd2_o==`MESI_ISC_CBUS_CMD_NOP);
cover property (@(posedge clk) cbus_cmd2_o==`MESI_ISC_CBUS_CMD_WR_SNOOP);
cover property (@(posedge clk) cbus_cmd2_o==`MESI_ISC_CBUS_CMD_RD_SNOOP);
cover property (@(posedge clk) cbus_cmd2_o==`MESI_ISC_CBUS_CMD_EN_WR);
cover property (@(posedge clk) cbus_cmd2_o==`MESI_ISC_CBUS_CMD_EN_RD);

cover property (@(posedge clk) cbus_cmd1_o==`MESI_ISC_CBUS_CMD_NOP);
cover property (@(posedge clk) cbus_cmd1_o==`MESI_ISC_CBUS_CMD_WR_SNOOP);
cover property (@(posedge clk) cbus_cmd1_o==`MESI_ISC_CBUS_CMD_RD_SNOOP);
cover property (@(posedge clk) cbus_cmd1_o==`MESI_ISC_CBUS_CMD_EN_WR);
cover property (@(posedge clk) cbus_cmd1_o==`MESI_ISC_CBUS_CMD_EN_RD);

cover property (@(posedge clk) cbus_cmd0_o==`MESI_ISC_CBUS_CMD_NOP);
cover property (@(posedge clk) cbus_cmd0_o==`MESI_ISC_CBUS_CMD_WR_SNOOP);
cover property (@(posedge clk) cbus_cmd0_o==`MESI_ISC_CBUS_CMD_RD_SNOOP);
cover property (@(posedge clk) cbus_cmd0_o==`MESI_ISC_CBUS_CMD_EN_WR);
cover property (@(posedge clk) cbus_cmd0_o==`MESI_ISC_CBUS_CMD_EN_RD);


cover property (@(posedge clk) broad_fifo_status_full);

endmodule


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
    broad_fifo_rd_o,
    // Internal Signals
    cbus_active_broad_array,
    cbus_active_en_access_array,
    broadcast_in_progress,
    broad_snoop_cpu_id
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
input [3:0] cbus_active_broad_array;
input [3:0] cbus_active_en_access_array;
input broadcast_in_progress;
input broad_snoop_cpu_id;

logic [CBUS_CMD_WIDTH-1:0] cbus_cmd3 = cbus_cmd_array_o[(3+1)*CBUS_CMD_WIDTH-1 : 3*CBUS_CMD_WIDTH];
logic [CBUS_CMD_WIDTH-1:0] cbus_cmd2 = cbus_cmd_array_o[(2+1)*CBUS_CMD_WIDTH-1 : 2*CBUS_CMD_WIDTH];
logic [CBUS_CMD_WIDTH-1:0] cbus_cmd1 = cbus_cmd_array_o[(1+1)*CBUS_CMD_WIDTH-1 : 1*CBUS_CMD_WIDTH];
logic [CBUS_CMD_WIDTH-1:0] cbus_cmd0 = cbus_cmd_array_o[(0+1)*CBUS_CMD_WIDTH-1 : 0*CBUS_CMD_WIDTH];

// Assume properties
//assume property (@(posedge clk) cbus_cmd3 != 3'd5);
//assume property (@(posedge clk) cbus_cmd3 != 3'd6);
//assume property (@(posedge clk) cbus_cmd3 != 3'd7);
//
//assume property (@(posedge clk) (broad_snoop_type_i == `MESI_ISC_BREQ_TYPE_RD) || (broad_snoop_type_i == `MESI_ISC_BREQ_TYPE_WR) || (broad_snoop_type_i == `MESI_ISC_BREQ_TYPE_NOP));
//assume property (@(posedge clk) (cbus_active_broad_array == 4'b0000) || (cbus_active_broad_array == 4'b1110) || (cbus_active_broad_array == 4'b1101) ||
//        (cbus_active_broad_array == 4'b1011) || (cbus_active_broad_array == 4'b0111) );
//assume property (@(posedge clk) (cbus_active_en_access_array == 4'b0000) || (cbus_active_en_access_array == 4'b0001) || (cbus_active_en_access_array == 4'b0010) ||
//        (cbus_active_en_access_array == 4'b0100) || (cbus_active_en_access_array == 4'b1000) );

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

logic [MBUS_CMD_WIDTH-1:0] mbus_cmd_array_i_3 = mbus_cmd_array_i[(3+1)*MBUS_CMD_WIDTH-1 : 3*MBUS_CMD_WIDTH];
logic [MBUS_CMD_WIDTH-1:0] mbus_cmd_array_i_2 = mbus_cmd_array_i[(2+1)*MBUS_CMD_WIDTH-1 : 2*MBUS_CMD_WIDTH];
logic [MBUS_CMD_WIDTH-1:0] mbus_cmd_array_i_1 = mbus_cmd_array_i[(1+1)*MBUS_CMD_WIDTH-1 : 1*MBUS_CMD_WIDTH];
logic [MBUS_CMD_WIDTH-1:0] mbus_cmd_array_i_0 = mbus_cmd_array_i[(0+1)*MBUS_CMD_WIDTH-1 : 0*MBUS_CMD_WIDTH];

//// Empty and full signals shouldn't be active at the same time
//assume property (@(posedge clk) !(fifo_status_empty_array_i[0] && fifo_status_full_array_i[0]));
//assume property (@(posedge clk) !(fifo_status_empty_array_i[1] && fifo_status_full_array_i[1]));
//assume property (@(posedge clk) !(fifo_status_empty_array_i[2] && fifo_status_full_array_i[2]));
//assume property (@(posedge clk) !(fifo_status_empty_array_i[3] && fifo_status_full_array_i[3]));
//
//// Broad type doesn't take the value 3
//assume property (@(posedge clk) broad_type_array_i[(3+1)*BROAD_TYPE_WIDTH-1 : 3*BROAD_TYPE_WIDTH] != 3);
//assume property (@(posedge clk) broad_type_array_i[(2+1)*BROAD_TYPE_WIDTH-1 : 2*BROAD_TYPE_WIDTH] != 3);
//assume property (@(posedge clk) broad_type_array_i[(1+1)*BROAD_TYPE_WIDTH-1 : 1*BROAD_TYPE_WIDTH] != 3);
//assume property (@(posedge clk) broad_type_array_i[(0+1)*BROAD_TYPE_WIDTH-1 : 0*BROAD_TYPE_WIDTH] != 3);
//
//// Mbus command doesn't take the values 5, 6, and 7
//assume property (@(posedge clk) mbus_cmd_array_i[(3+1)*MBUS_CMD_WIDTH-1 : 3*MBUS_CMD_WIDTH] != 5);
//assume property (@(posedge clk) mbus_cmd_array_i[(3+1)*MBUS_CMD_WIDTH-1 : 3*MBUS_CMD_WIDTH] != 6);
//assume property (@(posedge clk) mbus_cmd_array_i[(3+1)*MBUS_CMD_WIDTH-1 : 3*MBUS_CMD_WIDTH] != 7);
//
//assume property (@(posedge clk) mbus_cmd_array_i[(2+1)*MBUS_CMD_WIDTH-1 : 2*MBUS_CMD_WIDTH] != 5);
//assume property (@(posedge clk) mbus_cmd_array_i[(2+1)*MBUS_CMD_WIDTH-1 : 2*MBUS_CMD_WIDTH] != 6);
//assume property (@(posedge clk) mbus_cmd_array_i[(2+1)*MBUS_CMD_WIDTH-1 : 2*MBUS_CMD_WIDTH] != 7);
//
//assume property (@(posedge clk) mbus_cmd_array_i[(1+1)*MBUS_CMD_WIDTH-1 : 1*MBUS_CMD_WIDTH] != 5);
//assume property (@(posedge clk) mbus_cmd_array_i[(1+1)*MBUS_CMD_WIDTH-1 : 1*MBUS_CMD_WIDTH] != 6);
//assume property (@(posedge clk) mbus_cmd_array_i[(1+1)*MBUS_CMD_WIDTH-1 : 1*MBUS_CMD_WIDTH] != 7);
//
//assume property (@(posedge clk) mbus_cmd_array_i[(0+1)*MBUS_CMD_WIDTH-1 : 0*MBUS_CMD_WIDTH] != 5);
//assume property (@(posedge clk) mbus_cmd_array_i[(0+1)*MBUS_CMD_WIDTH-1 : 0*MBUS_CMD_WIDTH] != 6);
//assume property (@(posedge clk) mbus_cmd_array_i[(0+1)*MBUS_CMD_WIDTH-1 : 0*MBUS_CMD_WIDTH] != 7);


// Reset values for signals
assert property (@(posedge clk) $fell(rst) |-> fifo_wr_array_o == 0);
assert property (@(posedge clk) $fell(rst) |-> breq_type_array_o == 0);
assert property (@(posedge clk) $fell(rst) |-> breq_id_array_o[(3+1)*BROAD_ID_WIDTH-1 : 3*BROAD_ID_WIDTH] == 0);
assert property (@(posedge clk) $fell(rst) |-> breq_id_array_o[(2+1)*BROAD_ID_WIDTH-1 : 2*BROAD_ID_WIDTH] == 1);
assert property (@(posedge clk) $fell(rst) |-> breq_id_array_o[(1+1)*BROAD_ID_WIDTH-1 : 1*BROAD_ID_WIDTH] == 2);
assert property (@(posedge clk) $fell(rst) |-> breq_id_array_o[(0+1)*BROAD_ID_WIDTH-1 : 0*BROAD_ID_WIDTH] == 3);

// Acknowledge signal is high only for one cycle
assert property (@(posedge clk) disable iff(rst) mbus_ack_array_o[0] |=> !mbus_ack_array_o[0]);
assert property (@(posedge clk) disable iff(rst) mbus_ack_array_o[1] |=> !mbus_ack_array_o[1]);
assert property (@(posedge clk) disable iff(rst) mbus_ack_array_o[2] |=> !mbus_ack_array_o[2]);
assert property (@(posedge clk) disable iff(rst) mbus_ack_array_o[3] |=> !mbus_ack_array_o[3]);

// Assert ack signal only when it is a read or write broadcast command on the main bus
// and the fifo for that bus is not full and ack is not asserted in the previous cycle
assert property (@(posedge clk) disable iff(rst) 
        (mbus_cmd_array_i_3 == `MESI_ISC_MBUS_CMD_WR_BROAD |
        mbus_cmd_array_i_3 == `MESI_ISC_MBUS_CMD_RD_BROAD)
        & !fifo_status_full_array_i[3] & !mbus_ack_array_o[3] |=> mbus_ack_array_o[3]
);

assert property (@(posedge clk) disable iff(rst) 
        (mbus_cmd_array_i_2 == `MESI_ISC_MBUS_CMD_WR_BROAD |
        mbus_cmd_array_i_2 == `MESI_ISC_MBUS_CMD_RD_BROAD)
        & !fifo_status_full_array_i[2] & !mbus_ack_array_o[2] |=> mbus_ack_array_o[2]
);

assert property (@(posedge clk) disable iff(rst) 
        (mbus_cmd_array_i_1 == `MESI_ISC_MBUS_CMD_WR_BROAD |
        mbus_cmd_array_i_1 == `MESI_ISC_MBUS_CMD_RD_BROAD)
        & !fifo_status_full_array_i[1] & !mbus_ack_array_o[1] |=> mbus_ack_array_o[1]
);

assert property (@(posedge clk) disable iff(rst) 
        (mbus_cmd_array_i_0 == `MESI_ISC_MBUS_CMD_WR_BROAD |
        mbus_cmd_array_i_0 == `MESI_ISC_MBUS_CMD_RD_BROAD)
        & !fifo_status_full_array_i[0] & !mbus_ack_array_o[0] |=> mbus_ack_array_o[0]
);

// Liveness property for round robin arbiter - Request should be read in 4 cycles
assert property (@(posedge clk) disable iff (broad_fifo_status_full_i | fifo_status_empty_array_i[0]) 
    !fifo_status_empty_array_i[0] |-> ##[1:4] fifo_rd_array_o[0]
);

assert property (@(posedge clk) disable iff (broad_fifo_status_full_i | fifo_status_empty_array_i[1]) 
    !fifo_status_empty_array_i[1] |-> ##[1:4] fifo_rd_array_o[1]
);

assert property (@(posedge clk) disable iff (broad_fifo_status_full_i | fifo_status_empty_array_i[2]) 
    !fifo_status_empty_array_i[2] |-> ##[1:4] fifo_rd_array_o[2]
);

assert property (@(posedge clk) disable iff (broad_fifo_status_full_i | fifo_status_empty_array_i[3]) 
    !fifo_status_empty_array_i[3] |-> ##[1:4] fifo_rd_array_o[3]
);


// Read only from one FIFO at a time
assert property (@(posedge clk) disable iff(rst) $onehot0(fifo_rd_array_o));

// FIFO broadcast write should be only when we are reading from breq FIFO
assert property (@(posedge clk) disable iff(rst) |fifo_rd_array_o |-> broad_fifo_wr_o);
assert property (@(posedge clk) disable iff(rst) !(|fifo_rd_array_o) |-> !broad_fifo_wr_o);

// Fixed values for cpu_id are correct
assert property (@(posedge clk) breq_cpu_id_array_o[(3+1)*2-1 : 3*2] == 3);
assert property (@(posedge clk) breq_cpu_id_array_o[(2+1)*2-1 : 2*2] == 2);
assert property (@(posedge clk) breq_cpu_id_array_o[(1+1)*2-1 : 1*2] == 1);
assert property (@(posedge clk) breq_cpu_id_array_o[(0+1)*2-1 : 0*2] == 0);

//generate
//for (genvar i=0; i<4; i++) begin : assert_cpu_id
//    assert property (@(posedge clk) breq_cpu_id_array_o[(i+1)*2-1 : i*2] == i);
//end
//endgenerate

// Check breq_type_array_o is properly assigned
assert property (@(posedge clk) mbus_cmd_array_i_3[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_RD_BROAD
        |=> breq_type_array_o[(3+1)*BROAD_TYPE_WIDTH-1: 3*BROAD_TYPE_WIDTH] == `MESI_ISC_BREQ_TYPE_RD);
assert property (@(posedge clk) mbus_cmd_array_i_3[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_WR_BROAD
        |=> breq_type_array_o[(3+1)*BROAD_TYPE_WIDTH-1: 3*BROAD_TYPE_WIDTH] == `MESI_ISC_BREQ_TYPE_WR);
assert property (@(posedge clk) ((mbus_cmd_array_i_3[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_WR) ||
            (mbus_cmd_array_i_3[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_RD) || 
            (mbus_cmd_array_i_3[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_NOP))
        |=> breq_type_array_o[(3+1)*BROAD_TYPE_WIDTH-1: 3*BROAD_TYPE_WIDTH] == `MESI_ISC_BREQ_TYPE_NOP);

assert property (@(posedge clk) mbus_cmd_array_i_2[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_RD_BROAD
        |=> breq_type_array_o[(2+1)*BROAD_TYPE_WIDTH-1: 2*BROAD_TYPE_WIDTH] == `MESI_ISC_BREQ_TYPE_RD);
assert property (@(posedge clk) mbus_cmd_array_i_2[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_WR_BROAD
        |=> breq_type_array_o[(2+1)*BROAD_TYPE_WIDTH-1: 2*BROAD_TYPE_WIDTH] == `MESI_ISC_BREQ_TYPE_WR);
assert property (@(posedge clk) ((mbus_cmd_array_i_2[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_WR) ||
            (mbus_cmd_array_i_2[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_RD) || 
            (mbus_cmd_array_i_2[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_NOP))
        |=> breq_type_array_o[(2+1)*BROAD_TYPE_WIDTH-1: 2*BROAD_TYPE_WIDTH] == `MESI_ISC_BREQ_TYPE_NOP);

assert property (@(posedge clk) mbus_cmd_array_i_1[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_RD_BROAD
        |=> breq_type_array_o[(1+1)*BROAD_TYPE_WIDTH-1: 1*BROAD_TYPE_WIDTH] == `MESI_ISC_BREQ_TYPE_RD);
assert property (@(posedge clk) mbus_cmd_array_i_1[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_WR_BROAD
        |=> breq_type_array_o[(1+1)*BROAD_TYPE_WIDTH-1: 1*BROAD_TYPE_WIDTH] == `MESI_ISC_BREQ_TYPE_WR);
assert property (@(posedge clk) ((mbus_cmd_array_i_1[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_WR) ||
            (mbus_cmd_array_i_1[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_RD) || 
            (mbus_cmd_array_i_1[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_NOP))
        |=> breq_type_array_o[(1+1)*BROAD_TYPE_WIDTH-1: 1*BROAD_TYPE_WIDTH] == `MESI_ISC_BREQ_TYPE_NOP);

assert property (@(posedge clk) mbus_cmd_array_i_0[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_RD_BROAD
        |=> breq_type_array_o[(0+1)*BROAD_TYPE_WIDTH-1: 0*BROAD_TYPE_WIDTH] == `MESI_ISC_BREQ_TYPE_RD);
assert property (@(posedge clk) mbus_cmd_array_i_0[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_WR_BROAD
        |=> breq_type_array_o[(0+1)*BROAD_TYPE_WIDTH-1: 0*BROAD_TYPE_WIDTH] == `MESI_ISC_BREQ_TYPE_WR);
assert property (@(posedge clk) ((mbus_cmd_array_i_0[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_WR) ||
            (mbus_cmd_array_i_0[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_RD) || 
            (mbus_cmd_array_i_0[MBUS_CMD_WIDTH-1:0]==`MESI_ISC_MBUS_CMD_NOP))
        |=> breq_type_array_o[(0+1)*BROAD_TYPE_WIDTH-1: 0*BROAD_TYPE_WIDTH] == `MESI_ISC_BREQ_TYPE_NOP);


// FIFO are empty atleast once
cover property (@(posedge clk) fifo_status_empty_array_i[0]);
cover property (@(posedge clk) fifo_status_empty_array_i[1]);
cover property (@(posedge clk) fifo_status_empty_array_i[2]);
cover property (@(posedge clk) fifo_status_empty_array_i[3]);
cover property (@(posedge clk) fifo_status_empty_array_i);

// FIFO are full atleast once
cover property (@(posedge clk) fifo_status_full_array_i[0]);
cover property (@(posedge clk) fifo_status_full_array_i[1]);
cover property (@(posedge clk) fifo_status_full_array_i[2]);
cover property (@(posedge clk) fifo_status_full_array_i[3]);
cover property (@(posedge clk) fifo_status_full_array_i);

// Broad FIFO is full
cover property (@(posedge clk) broad_fifo_status_full_i);

// All mbus commands are covered atleast once
cover property (@(posedge clk) mbus_cmd_array_i_3 == `MESI_ISC_MBUS_CMD_WR_BROAD);
cover property (@(posedge clk) mbus_cmd_array_i_3 == `MESI_ISC_MBUS_CMD_RD_BROAD);
cover property (@(posedge clk) mbus_cmd_array_i_3 == `MESI_ISC_MBUS_CMD_WR);
cover property (@(posedge clk) mbus_cmd_array_i_3 == `MESI_ISC_MBUS_CMD_RD);
cover property (@(posedge clk) mbus_cmd_array_i_3 == `MESI_ISC_MBUS_CMD_NOP);

cover property (@(posedge clk) mbus_cmd_array_i_2 == `MESI_ISC_MBUS_CMD_WR_BROAD);
cover property (@(posedge clk) mbus_cmd_array_i_2 == `MESI_ISC_MBUS_CMD_RD_BROAD);
cover property (@(posedge clk) mbus_cmd_array_i_2 == `MESI_ISC_MBUS_CMD_WR);
cover property (@(posedge clk) mbus_cmd_array_i_2 == `MESI_ISC_MBUS_CMD_RD);
cover property (@(posedge clk) mbus_cmd_array_i_2 == `MESI_ISC_MBUS_CMD_NOP);

cover property (@(posedge clk) mbus_cmd_array_i_1 == `MESI_ISC_MBUS_CMD_WR_BROAD);
cover property (@(posedge clk) mbus_cmd_array_i_1 == `MESI_ISC_MBUS_CMD_RD_BROAD);
cover property (@(posedge clk) mbus_cmd_array_i_1 == `MESI_ISC_MBUS_CMD_WR);
cover property (@(posedge clk) mbus_cmd_array_i_1 == `MESI_ISC_MBUS_CMD_RD);
cover property (@(posedge clk) mbus_cmd_array_i_1 == `MESI_ISC_MBUS_CMD_NOP);

cover property (@(posedge clk) mbus_cmd_array_i_0 == `MESI_ISC_MBUS_CMD_WR_BROAD);
cover property (@(posedge clk) mbus_cmd_array_i_0 == `MESI_ISC_MBUS_CMD_RD_BROAD);
cover property (@(posedge clk) mbus_cmd_array_i_0 == `MESI_ISC_MBUS_CMD_WR);
cover property (@(posedge clk) mbus_cmd_array_i_0 == `MESI_ISC_MBUS_CMD_RD);
cover property (@(posedge clk) mbus_cmd_array_i_0 == `MESI_ISC_MBUS_CMD_NOP);

// Read a breq and write to broad FIFO operations are happening atleast once
cover property (@(posedge clk) fifo_rd_array_o[0]);
cover property (@(posedge clk) fifo_rd_array_o[1]);
cover property (@(posedge clk) fifo_rd_array_o[2]);
cover property (@(posedge clk) fifo_rd_array_o[3]);

cover property (@(posedge clk) fifo_wr_array_o[0]);
cover property (@(posedge clk) fifo_wr_array_o[1]);
cover property (@(posedge clk) fifo_wr_array_o[2]);
cover property (@(posedge clk) fifo_wr_array_o[3]);

cover property (@(posedge clk) broad_fifo_wr_o);


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
input [FIFO_SIZE_LOG2-1:0] fifo_depth;

logic [FIFO_SIZE_LOG2-1:0] ptr_wr_updt = ptr_wr + {(FIFO_SIZE_LOG2){1'b1}};   //ptr_wr-1
logic [FIFO_SIZE_LOG2-1:0] ptr_rd_updt = ptr_rd + {(FIFO_SIZE_LOG2){1'b1}};   //ptr_rd-1 

// Shouldn't read when FIFO is empty and shouldn't write when it is full
//assume property (@(posedge clk) status_empty_o |-> !rd_i);
//assume property (@(posedge clk) status_full_o |-> !wr_i);
//
//// Assume that the input data is known and stable when writing
//// Assume that the output data is known and stable when reading a non-empty FIFO
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

//assume property (@(posedge clk) broad_type_o != 3);
//
//assume property (@(posedge clk) mbus_cmd_array_i_3 != 5);
//assume property (@(posedge clk) mbus_cmd_array_i_3 != 6);
//assume property (@(posedge clk) mbus_cmd_array_i_3 != 7);
//
//assume property (@(posedge clk) mbus_cmd_array_i_2 != 5);
//assume property (@(posedge clk) mbus_cmd_array_i_2 != 6);
//assume property (@(posedge clk) mbus_cmd_array_i_2 != 7);
//
//assume property (@(posedge clk) mbus_cmd_array_i_1 != 5);
//assume property (@(posedge clk) mbus_cmd_array_i_1 != 6);
//assume property (@(posedge clk) mbus_cmd_array_i_1 != 7);
//
//assume property (@(posedge clk) mbus_cmd_array_i_0 != 5);
//assume property (@(posedge clk) mbus_cmd_array_i_0 != 6);
//assume property (@(posedge clk) mbus_cmd_array_i_0 != 7);

assert property (@(posedge clk) fifo_status_empty_array[0] |-> !fifo_rd_array[0]);
assert property (@(posedge clk) fifo_status_empty_array[1] |-> !fifo_rd_array[1]);
assert property (@(posedge clk) fifo_status_empty_array[2] |-> !fifo_rd_array[2]);
assert property (@(posedge clk) fifo_status_empty_array[3] |-> !fifo_rd_array[3]);

assert property (@(posedge clk) fifo_status_full_array[3] |-> !fifo_wr_array[3]);
assert property (@(posedge clk) fifo_status_full_array[2] |-> !fifo_wr_array[2]);
assert property (@(posedge clk) fifo_status_full_array[1] |-> !fifo_wr_array[1]);
assert property (@(posedge clk) fifo_status_full_array[0] |-> !fifo_wr_array[0]);

assert property (@(posedge clk) disable iff(broad_fifo_status_full_i | fifo_status_empty_array[0]) mbus_cmd_array_i_0==`MESI_ISC_MBUS_CMD_RD  |-> ##[1:4] (fifo_rd_array[0]));
assert property (@(posedge clk) disable iff(broad_fifo_status_full_i | fifo_status_empty_array[1]) mbus_cmd_array_i_1==`MESI_ISC_MBUS_CMD_RD  |-> ##[1:4] (fifo_rd_array[1]));
assert property (@(posedge clk) disable iff(broad_fifo_status_full_i | fifo_status_empty_array[2]) mbus_cmd_array_i_2==`MESI_ISC_MBUS_CMD_RD  |-> ##[1:4] (fifo_rd_array[2]));
assert property (@(posedge clk) disable iff(broad_fifo_status_full_i | fifo_status_empty_array[3]) mbus_cmd_array_i_3==`MESI_ISC_MBUS_CMD_RD  |-> ##[1:4] (fifo_rd_array[3]));

assert property (@(posedge clk) fifo_rd_array[0] |-> broad_cpu_id_o==0);
assert property (@(posedge clk) fifo_rd_array[1] |-> broad_cpu_id_o==1);
assert property (@(posedge clk) fifo_rd_array[2] |-> broad_cpu_id_o==2);
assert property (@(posedge clk) fifo_rd_array[3] |-> broad_cpu_id_o==3);

assert property (@(posedge clk) disable iff(rst) mbus_ack_array_o[0] |=> !mbus_ack_array_o[0]);
assert property (@(posedge clk) disable iff(rst) mbus_ack_array_o[1] |=> !mbus_ack_array_o[1]);
assert property (@(posedge clk) disable iff(rst) mbus_ack_array_o[2] |=> !mbus_ack_array_o[2]);
assert property (@(posedge clk) disable iff(rst) mbus_ack_array_o[3] |=> !mbus_ack_array_o[3]);


assert property (@(posedge clk) broad_fifo_status_full_i |-> !broad_fifo_wr_o);

endmodule   


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
  BROAD_ID_WIDTH           = 7,  
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

// Assert
assert property (@(posedge clk) fifo_status_full_o |-> !broad_fifo_wr_i);

// Other properties are similar to the broad controller
// as there is no extra logic in this module aside from that and a FIFO

// Cover properties 
cover property (@(posedge clk) broad_fifo_wr_i);
cover property (@(posedge clk) fifo_status_full_o);

cover property (@(posedge clk) broad_cpu_id_i ==0);
cover property (@(posedge clk) broad_cpu_id_i ==1);
cover property (@(posedge clk) broad_cpu_id_i ==2);
cover property (@(posedge clk) broad_cpu_id_i ==3);

endmodule   


module Wrapper;

bind mesi_isc mesi_isc_props wrp_mesi_isc (
     .clk(clk),
     .rst(rst),
     .mbus_cmd3_i(mbus_cmd3_i),
     .mbus_cmd2_i(mbus_cmd2_i),
     .mbus_cmd1_i(mbus_cmd1_i),
     .mbus_cmd0_i(mbus_cmd0_i),
     .mbus_addr3_i(mbus_addr3_i),
     .mbus_addr2_i(mbus_addr2_i),
     .mbus_addr1_i(mbus_addr1_i),
     .mbus_addr0_i(mbus_addr0_i),
     .cbus_ack3_i(cbus_ack3_i),
     .cbus_ack2_i(cbus_ack2_i),
     .cbus_ack1_i(cbus_ack1_i),
     .cbus_ack0_i(cbus_ack0_i),
     .cbus_addr_o(cbus_addr_o),
     .cbus_cmd3_o(cbus_cmd3_o),
     .cbus_cmd2_o(cbus_cmd2_o),
     .cbus_cmd1_o(cbus_cmd1_o),
     .cbus_cmd0_o(cbus_cmd0_o),
     .mbus_ack3_o(mbus_ack3_o),
     .mbus_ack2_o(mbus_ack2_o),
     .mbus_ack1_o(mbus_ack1_o),
     .mbus_ack0_o(mbus_ack0_o),
     .broad_fifo_status_full(broad_fifo_status_full),
     .fifo_status_empty_array(mesi_isc_breq_fifos.fifo_status_empty_array)
);   


bind mesi_isc breq_fifos_props #(MBUS_CMD_WIDTH,
                      ADDR_WIDTH,
                      BROAD_TYPE_WIDTH,  
                      BROAD_ID_WIDTH,  
                      BREQ_FIFO_SIZE,
                      BREQ_FIFO_SIZE_LOG2) wrp_breq  (
    .clk(mesi_isc_breq_fifos.clk),
    .rst(mesi_isc_breq_fifos.rst),
    .mbus_cmd_array_i(mesi_isc_breq_fifos.mbus_cmd_array_i),
    .mbus_addr_array_i(mesi_isc_breq_fifos.mbus_addr_array_i),
    .broad_fifo_status_full_i(mesi_isc_breq_fifos.broad_fifo_status_full_i),
    .mbus_ack_array_o(mesi_isc_breq_fifos.mbus_ack_array_o),
    .broad_fifo_wr_o(mesi_isc_breq_fifos.broad_fifo_wr_o),
    .broad_addr_o(mesi_isc_breq_fifos.broad_addr_o),
    .broad_type_o(mesi_isc_breq_fifos.broad_type_o),
    .broad_cpu_id_o(mesi_isc_breq_fifos.broad_cpu_id_o),
    .broad_id_o(mesi_isc_breq_fifos.broad_id_o),
    .fifo_wr_array(mesi_isc_breq_fifos.fifo_wr_array),
    .fifo_rd_array(mesi_isc_breq_fifos.fifo_rd_array),
    .fifo_status_empty_array(mesi_isc_breq_fifos.fifo_status_empty_array),
    .fifo_status_full_array(mesi_isc_breq_fifos.fifo_status_full_array)
);

bind mesi_isc mesi_isc_fifo_props #(
                      ADDR_WIDTH + BROAD_TYPE_WIDTH + 2 +BROAD_ID_WIDTH,  
                      BREQ_FIFO_SIZE,
                      BREQ_FIFO_SIZE_LOG2) wrp_mesi_isc_fifo_0 (
    .clk(clk),
    .rst(rst),
    .wr_i(mesi_isc_breq_fifos.fifo_0.wr_i),
    .rd_i(mesi_isc_breq_fifos.fifo_0.rd_i),
    .data_i(mesi_isc_breq_fifos.fifo_0.data_i),
    .data_o(mesi_isc_breq_fifos.fifo_0.data_o),
    .status_empty_o(mesi_isc_breq_fifos.fifo_0.status_empty_o),
    .status_full_o(mesi_isc_breq_fifos.fifo_0.status_full_o),
    .ptr_wr(mesi_isc_breq_fifos.fifo_0.ptr_wr),
    .ptr_rd(mesi_isc_breq_fifos.fifo_0.ptr_rd),
    .fifo_depth(mesi_isc_breq_fifos.fifo_0.fifo_depth)
);

bind mesi_isc mesi_isc_fifo_props #(
                      ADDR_WIDTH + BROAD_TYPE_WIDTH + 2 +BROAD_ID_WIDTH,  
                      BREQ_FIFO_SIZE,
                      BREQ_FIFO_SIZE_LOG2) wrp_mesi_isc_fifo_1 (
    .clk(clk),
    .rst(rst),
    .wr_i(mesi_isc_breq_fifos.fifo_1.wr_i),
    .rd_i(mesi_isc_breq_fifos.fifo_1.rd_i),
    .data_i(mesi_isc_breq_fifos.fifo_1.data_i),
    .data_o(mesi_isc_breq_fifos.fifo_1.data_o),
    .status_empty_o(mesi_isc_breq_fifos.fifo_1.status_empty_o),
    .status_full_o(mesi_isc_breq_fifos.fifo_1.status_full_o),
    .ptr_wr(mesi_isc_breq_fifos.fifo_1.ptr_wr),
    .ptr_rd(mesi_isc_breq_fifos.fifo_1.ptr_rd),
    .fifo_depth(mesi_isc_breq_fifos.fifo_1.fifo_depth)
);
    
bind mesi_isc mesi_isc_fifo_props #(
                      ADDR_WIDTH + BROAD_TYPE_WIDTH + 2 +BROAD_ID_WIDTH,  
                      BREQ_FIFO_SIZE,
                      BREQ_FIFO_SIZE_LOG2) wrp_mesi_isc_fifo_2 (
    .clk(clk),
    .rst(rst),
    .wr_i(mesi_isc_breq_fifos.fifo_2.wr_i),
    .rd_i(mesi_isc_breq_fifos.fifo_2.rd_i),
    .data_i(mesi_isc_breq_fifos.fifo_2.data_i),
    .data_o(mesi_isc_breq_fifos.fifo_2.data_o),
    .status_empty_o(mesi_isc_breq_fifos.fifo_2.status_empty_o),
    .status_full_o(mesi_isc_breq_fifos.fifo_2.status_full_o),
    .ptr_wr(mesi_isc_breq_fifos.fifo_2.ptr_wr),
    .ptr_rd(mesi_isc_breq_fifos.fifo_2.ptr_rd),
    .fifo_depth(mesi_isc_breq_fifos.fifo_2.fifo_depth)
);

bind mesi_isc mesi_isc_fifo_props #(
                      ADDR_WIDTH + BROAD_TYPE_WIDTH + 2 +BROAD_ID_WIDTH,  
                      BREQ_FIFO_SIZE,
                      BREQ_FIFO_SIZE_LOG2) wrp_mesi_isc_fifo_3 (
    .clk(clk),
    .rst(rst),
    .wr_i(mesi_isc_breq_fifos.fifo_3.wr_i),
    .rd_i(mesi_isc_breq_fifos.fifo_3.rd_i),
    .data_i(mesi_isc_breq_fifos.fifo_3.data_i),
    .data_o(mesi_isc_breq_fifos.fifo_3.data_o),
    .status_empty_o(mesi_isc_breq_fifos.fifo_3.status_empty_o),
    .status_full_o(mesi_isc_breq_fifos.fifo_3.status_full_o),
    .ptr_wr(mesi_isc_breq_fifos.fifo_3.ptr_wr),
    .ptr_rd(mesi_isc_breq_fifos.fifo_3.ptr_rd),
    .fifo_depth(mesi_isc_breq_fifos.fifo_3.fifo_depth)
);
    
bind mesi_isc breq_fifos_cntl_props #(MBUS_CMD_WIDTH,
                           ADDR_WIDTH,
                           BROAD_TYPE_WIDTH,
                           BROAD_ID_WIDTH) wrp_breq_cntl (
    .clk(clk),
    .rst(rst),
    .mbus_cmd_array_i(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.mbus_cmd_array_i),
    .fifo_status_empty_array_i(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.fifo_status_empty_array_i),
    .fifo_status_full_array_i(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.fifo_status_full_array_i),
    .broad_fifo_status_full_i(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.broad_fifo_status_full_i),
    .broad_addr_array_i(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.broad_addr_array_i),
    .broad_type_array_i(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.broad_type_array_i),
    .broad_id_array_i(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.broad_id_array_i),
    .mbus_ack_array_o(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.mbus_ack_array_o),
    .fifo_wr_array_o(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.fifo_wr_array_o),
    .fifo_rd_array_o(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.fifo_rd_array_o),
    .broad_fifo_wr_o(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.broad_fifo_wr_o),
    .broad_addr_o(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.broad_addr_o),
    .broad_type_o(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.broad_type_o),
    .broad_cpu_id_o(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.broad_cpu_id_o),
    .broad_id_o(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.broad_id_o),
    .breq_type_array_o(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.breq_type_array_o),
    .breq_cpu_id_array_o(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.breq_cpu_id_array_o),
    .breq_id_array_o(mesi_isc_breq_fifos.mesi_isc_breq_fifos_cntl.breq_id_array_o)
);

bind mesi_isc broad_props #(CBUS_CMD_WIDTH,
                 ADDR_WIDTH,
                 BROAD_TYPE_WIDTH,  
                 BROAD_ID_WIDTH,  
                 BROAD_REQ_FIFO_SIZE,
                 BROAD_REQ_FIFO_SIZE_LOG2) wrp_broad (
     .clk(mesi_isc_broad.clk),
     .rst(mesi_isc_broad.rst),
     .cbus_ack_array_i(mesi_isc_broad.cbus_ack_array_i),
     .broad_fifo_wr_i(mesi_isc_broad.broad_fifo_wr_i),
     .broad_addr_i(mesi_isc_broad.broad_addr_i),
     .broad_type_i(mesi_isc_broad.broad_type_i),
     .broad_cpu_id_i(mesi_isc_broad.broad_cpu_id_i),
     .broad_id_i(mesi_isc_broad.broad_id_i),
     .cbus_addr_o(mesi_isc_broad.cbus_addr_o),
     .cbus_cmd_array_o(mesi_isc_broad.cbus_cmd_array_o),
     .fifo_status_full_o(mesi_isc_broad.fifo_status_full_o)
);

bind mesi_isc_broad_cntl broad_cntl_props #(CBUS_CMD_WIDTH,
                      BROAD_TYPE_WIDTH,
                      BROAD_ID_WIDTH) wrp_broad_cntl (
    .clk(clk),
    .rst(rst),
    .cbus_ack_array_i(mesi_isc_broad.mesi_isc_broad_cntl.cbus_ack_array_i),
    .fifo_status_empty_i(mesi_isc_broad.mesi_isc_broad_cntl.fifo_status_empty_i),
    .fifo_status_full_i(mesi_isc_broad.mesi_isc_broad_cntl.fifo_status_full_i),
    .broad_snoop_type_i(mesi_isc_broad.mesi_isc_broad_cntl.broad_snoop_type_i),
    .broad_snoop_cpu_id_i(mesi_isc_broad.mesi_isc_broad_cntl.broad_snoop_cpu_id_i),
    .broad_snoop_id_i(mesi_isc_broad.mesi_isc_broad_cntl.broad_snoop_id_i),
    .cbus_cmd_array_o(mesi_isc_broad.mesi_isc_broad_cntl.cbus_cmd_array_o),
    .broad_fifo_rd_o(mesi_isc_broad.mesi_isc_broad_cntl.broad_fifo_rd_o),
    .cbus_active_broad_array(mesi_isc_broad.mesi_isc_broad_cntl.cbus_active_broad_array),
    .cbus_active_en_access_array(mesi_isc_broad.mesi_isc_broad_cntl.cbus_active_en_access_array),
    .broadcast_in_progress(mesi_isc_broad.mesi_isc_broad_cntl.broadcast_in_progress)
);

bind mesi_isc mesi_isc_fifo_props #(
                      ADDR_WIDTH + BROAD_TYPE_WIDTH + 2 +BROAD_ID_WIDTH,  
                      BROAD_REQ_FIFO_SIZE,
                      BROAD_REQ_FIFO_SIZE_LOG2) wrp_mesi_isc_fifo_broad (
    .clk(clk),
    .rst(rst),
    .wr_i(mesi_isc_broad.broad_fifo.wr_i),
    .rd_i(mesi_isc_broad.broad_fifo.rd_i),
    .data_i(mesi_isc_broad.broad_fifo.data_i),
    .data_o(mesi_isc_broad.broad_fifo.data_o),
    .status_empty_o(mesi_isc_broad.broad_fifo.status_empty_o),
    .status_full_o(mesi_isc_broad.broad_fifo.status_full_o),
    .ptr_wr(mesi_isc_broad.broad_fifo.ptr_wr),
    .ptr_rd(mesi_isc_broad.broad_fifo.ptr_rd),
    .fifo_depth(mesi_isc_broad.broad_fifo.fifo_depth)
);

endmodule
