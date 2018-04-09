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

// Empty and full signals shouldn't be active at the same time
assume property (@(posedge clk) !(fifo_status_empty_array_i[0] && fifo_status_full_array_i[0]));
assume property (@(posedge clk) !(fifo_status_empty_array_i[1] && fifo_status_full_array_i[1]));
assume property (@(posedge clk) !(fifo_status_empty_array_i[2] && fifo_status_full_array_i[2]));
assume property (@(posedge clk) !(fifo_status_empty_array_i[3] && fifo_status_full_array_i[3]));

// Broad type doesn't take the value 3
assume property (@(posedge clk) broad_type_array_i[(3+1)*BROAD_TYPE_WIDTH-1 : 3*BROAD_TYPE_WIDTH] != 3);
assume property (@(posedge clk) broad_type_array_i[(2+1)*BROAD_TYPE_WIDTH-1 : 2*BROAD_TYPE_WIDTH] != 3);
assume property (@(posedge clk) broad_type_array_i[(1+1)*BROAD_TYPE_WIDTH-1 : 1*BROAD_TYPE_WIDTH] != 3);
assume property (@(posedge clk) broad_type_array_i[(0+1)*BROAD_TYPE_WIDTH-1 : 0*BROAD_TYPE_WIDTH] != 3);

// Mbus command doesn't take the values 5, 6, and 7
assume property (@(posedge clk) mbus_cmd_array_i[(3+1)*MBUS_CMD_WIDTH-1 : 3*MBUS_CMD_WIDTH] != 5);
assume property (@(posedge clk) mbus_cmd_array_i[(3+1)*MBUS_CMD_WIDTH-1 : 3*MBUS_CMD_WIDTH] != 6);
assume property (@(posedge clk) mbus_cmd_array_i[(3+1)*MBUS_CMD_WIDTH-1 : 3*MBUS_CMD_WIDTH] != 7);

assume property (@(posedge clk) mbus_cmd_array_i[(2+1)*MBUS_CMD_WIDTH-1 : 2*MBUS_CMD_WIDTH] != 5);
assume property (@(posedge clk) mbus_cmd_array_i[(2+1)*MBUS_CMD_WIDTH-1 : 2*MBUS_CMD_WIDTH] != 6);
assume property (@(posedge clk) mbus_cmd_array_i[(2+1)*MBUS_CMD_WIDTH-1 : 2*MBUS_CMD_WIDTH] != 7);

assume property (@(posedge clk) mbus_cmd_array_i[(1+1)*MBUS_CMD_WIDTH-1 : 1*MBUS_CMD_WIDTH] != 5);
assume property (@(posedge clk) mbus_cmd_array_i[(1+1)*MBUS_CMD_WIDTH-1 : 1*MBUS_CMD_WIDTH] != 6);
assume property (@(posedge clk) mbus_cmd_array_i[(1+1)*MBUS_CMD_WIDTH-1 : 1*MBUS_CMD_WIDTH] != 7);

assume property (@(posedge clk) mbus_cmd_array_i[(0+1)*MBUS_CMD_WIDTH-1 : 0*MBUS_CMD_WIDTH] != 5);
assume property (@(posedge clk) mbus_cmd_array_i[(0+1)*MBUS_CMD_WIDTH-1 : 0*MBUS_CMD_WIDTH] != 6);
assume property (@(posedge clk) mbus_cmd_array_i[(0+1)*MBUS_CMD_WIDTH-1 : 0*MBUS_CMD_WIDTH] != 7);


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

// Liveness property for round robin arbiter
//assert property (@(posedge clk)  |-> ##[1:4] fifo_rd_array_o[0]);

// Read only from one FIFO at a time
assert property (@(posedge clk) disable iff(rst) $onehot0(fifo_rd_array_o));

// FIFO broadcast write should be only when we are reading from breq FIFO
assert property (@(posedge clk) disable iff(rst) |fifo_rd_array_o |-> broad_fifo_wr_o);
assert property (@(posedge clk) disable iff(rst) !(|fifo_rd_array_o) |-> !broad_fifo_wr_o);


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


endmodule   



module Wrapper;


bind mesi_isc_breq_fifos_cntl breq_fifos_cntl_props  wrp_breq_cntl (
    .clk(clk),
    .rst(rst),
    .mbus_cmd_array_i(mbus_cmd_array_i),
    .fifo_status_empty_array_i(fifo_status_empty_array_i),
    .fifo_status_full_array_i(fifo_status_full_array_i),
    .broad_fifo_status_full_i(broad_fifo_status_full_i),
    .broad_addr_array_i(broad_addr_array_i),
    .broad_type_array_i(broad_type_array_i),
    .broad_id_array_i(broad_id_array_i),
    .mbus_ack_array_o(mbus_ack_array_o),
    .fifo_wr_array_o(fifo_wr_array_o),
    .fifo_rd_array_o(fifo_rd_array_o),
    .broad_fifo_wr_o(broad_fifo_wr_o),
    .broad_addr_o(broad_addr_o),
    .broad_type_o(broad_type_o),
    .broad_cpu_id_o(broad_cpu_id_o),
    .broad_id_o(broad_id_o),
    .breq_type_array_o(breq_type_array_o),
    .breq_cpu_id_array_o(breq_cpu_id_array_o),
    .breq_id_array_o(breq_id_array_o)
);


endmodule
