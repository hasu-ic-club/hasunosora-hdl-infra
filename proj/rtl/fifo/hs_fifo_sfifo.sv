//+FHDR------------------------------------------------------------------
// Copyright (C) 2025 Hasunosora IC Design Club
// MIT License
// Permission is hereby granted, free of charge, to any person obtaining a 
// copy of this design and associated documentation files (the “Design”), 
// to deal in the Design without restriction, including without limitation 
// the rights to use, copy, modify, merge, publish, distribute, sublicense, 
// and/or sell copies of the Design, and to permit persons to whom the 
// Design is furnished to do so, subject to the following conditions:
// The above copyright notice and this permission notice shall be included 
// in all copies or substantial portions of the Design.
//
// THE DESIGN IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, 
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF 
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. 
// IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, 
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, 
// TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE 
// DESIGN OR THE USE OR OTHER DEALINGS IN THE DESIGN.
//-----------------------------------------------------------------------
// FILE NAME: hs_fifo_sfifo.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-----------------------------------------------------------------------
// RELEASE VERSION:     0.1a0
// VERSION DESCRIPTION: Initial version
//-------------------------------------------------------------------------
// PURPOSE: Parameterized Synchronous FIFO
//          This design referenced the design in 
//                https://github.com/hdl-modules/hdl-modules. 
//          I translated the VHDL to SystemVerilog and modify some comments 
//          and design implementations. I respect and must thank contributors 
//          of hdl-modules, who provides so beautiful and reliable design in VHDL, 
//          that I can learn many things from it. 
// 
//          The significant changes is I add read detection logic to provide
//          the WREADY in packet mode. When the read side handshake occurs w/o
//          peek, the WREADY should not be de-asserted because there at least
//          one word is removed from FIFO.
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME   RANGE        DESCRIPTION                   DEFAULT VALUE
// DATA_TYPE        type         Type of data in FIFO          logic
// FIFO_DEPTH       2-16777216   Maximum depth of the FIFO     16
// ALMOST_FULL_LVL  0-FIFO_DEPTH Level to show 'almost full'   FIFO_DEPTH
// ALMOST_EMPTY_LVL 0-FIFO_DEPTH Level to show 'almost empty'  0
// EN_LAST_SIGNAL   bool_e       If true, user can use 'last'  BOOL_FALSE
//                               signals
// EN_PACKET_MODE   bool_e       If true, 'read_valid' will    BOOL_FALSE
//                               not be asserted until a full
//                               packet is available in FIFO
// EN_DROP_PACKET   bool_e       If true, user can use 'wdrop' BOOL_FALSE
//                               port
// EN_PEEK_MODE     bool_e       If true, use can read words   BOOL_FALSE
//                               w/o popping from FIFO by use 
//                               the 'rpeek' port
// EN_OUTPUT_REG    bool_e       Use an extra output register  BOOL_FALSE
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// Parameterized Synchronous FIFO
module hs_fifo_sfifo
import hs_ifr_misc_typedefs_pkg::*;
#(
    parameter type   DATA_TYPE        = logic,
    parameter int    FIFO_DEPTH       = 16,
    parameter int    ALMOST_FULL_LVL  = FIFO_DEPTH,
    parameter int    ALMOST_EMPTY_LVL = 0,
    parameter bool_e EN_LAST_SIGNAL   = BOOL_FALSE,
    parameter bool_e EN_PACKET_MODE   = BOOL_FALSE,
    parameter bool_e EN_DROP_PACKET   = BOOL_FALSE,
    parameter bool_e EN_PEEK_MODE     = BOOL_FALSE,
    parameter bool_e EN_OUTPUT_REG    = BOOL_FALSE,
    `LP_MODULE int FIFO_LEVEL_WIDTH = $clog2(FIFO_DEPTH + 1)
)
(
    // Clock & reset
    input  logic                              clk,
    input  logic                              aresetn,      // Note: The reset only reset control logic

    // Write side
    input  logic                              wvalid,
    output logic                              wready,
    input  DATA_TYPE                          wdata,
    input  logic                              wlast,
    input  logic                              wdrop,
    output logic                              walmost_full,

    // Read side
    input  logic                              rready,
    output logic                              rvalid,
    output DATA_TYPE                          rdata,
    output logic                              rlast,
    input  logic                              rpeek,
    output logic                              ralmost_empty,

    // Internal signals
    output logic     [FIFO_LEVEL_WIDTH - 1:0] level
);

// Assertions
`GENERATE_START
if (2 ** $clog2(FIFO_DEPTH) != FIFO_DEPTH) begin : assert_dep_pwr_2
    initial $fatal(1, "Depth (%0d) is not a power of 2.", FIFO_DEPTH);
end :assert_dep_pwr_2

if ((EN_LAST_SIGNAL == BOOL_FALSE) && (EN_PACKET_MODE == BOOL_TRUE)) begin : assert_pkt_mode_last
    initial $fatal(1, "Must enable last signal for Packet Mode.");
end : assert_pkt_mode_last

if ((EN_DROP_PACKET == BOOL_TRUE) && (EN_PACKET_MODE == BOOL_FALSE)) begin : assert_drop_pkt_mode
    initial $fatal(1, "Must enable packet mode for enable Drop Packet.");
end : assert_drop_pkt_mode


if ((EN_PEEK_MODE == BOOL_TRUE) && (EN_PACKET_MODE == BOOL_FALSE)) begin : assert_peek_pkt_mode
    initial $fatal(1, "Must enable packet mode for enable Peek Mode.");
end : assert_peek_pkt_mode


if ((EN_PEEK_MODE == BOOL_TRUE) && (EN_OUTPUT_REG == BOOL_TRUE)) begin : assert_peek_no_out_reg
    initial $fatal(1, "Output Register in not supported Peek Mode.");
end : assert_peek_no_out_reg
`GENERATE_END

localparam  int MEM_ACT_DEPTH              = FIFO_DEPTH - ((EN_OUTPUT_REG == BOOL_TRUE) ? 1 : 0);
localparam  int MEM_ADDR_WIDTH             = $clog2(MEM_ACT_DEPTH);
localparam  int MEM_ADDR_EXTEND            = MEM_ADDR_WIDTH + 1;

// The FIFO level number needs to be in range [0, FIFO_DEPTH]
typedef logic [FIFO_LEVEL_WIDTH - 1:0] fifo_lvl_t;
// Extra bits in the addresses to be able to make the distinction if the FIFO is full/empty
typedef logic [MEM_ADDR_EXTEND - 1:0] fifo_addr_t;
// The part of the address that actually goes to the RAM
typedef logic [MEM_ADDR_WIDTH - 1:0] mem_addr_t;

// Data packet with last signal
typedef struct packed
{
    logic tlast;
    DATA_TYPE data;
} fifo_data_w_last_s;

// FIFO level
fifo_lvl_t      fifo_level;
fifo_lvl_t      fifo_level_next;
fifo_addr_t     wr_rd_addr_diff;

// Flag to indicate there is a word in output register
logic           data_in_outff;
logic           data_in_outff_next;

// Read addresses
fifo_addr_t     read_addr_next;
fifo_addr_t     read_addr;
fifo_addr_t     read_addr_peek;

// Read address for calculating the FIFO level
// Under peek mode, the read address is not updated when peeking
fifo_addr_t     read_addr_c_level;

// Write addresses
fifo_addr_t     write_addr_next;
fifo_addr_t     write_addr;
fifo_addr_t     write_addr_next_no_drop;

// Address to store the start of packet for drop packet
// When dropping a packet, the write address will return to this address
fifo_addr_t     write_addr_sop;

// Handshake signals
logic           read_handshake;
logic           write_handshake;
logic           ram_read_handshake;

// Drop & peek signal
logic           need_drop;
logic           need_peek;

// Packet flags
fifo_lvl_t      num_lasts_in_fifo;
fifo_lvl_t      num_lasts_in_fifo_next;
logic           full_pkt_est;
logic           full_pkt_est_lat1;
// Indicated a write transaction occurred and write in a LAST signal
logic           pkt_last_write_trans;
logic           pkt_last_write_trans_lat1;
// Indicated a read transaction (but not peek) occurred and read out a LAST signal
logic           pkt_last_read_trans_nopeek;

// Internal signals
logic           wready_int;
logic           rvalid_int;
logic           rlast_int;

logic           wready_next;

// RAM signals
mem_addr_t      ram_waddr;
mem_addr_t      ram_raddr;

logic           ram_wen;

logic           ram_rvalid_req;
logic           ram_rready;
logic           ram_rvalid;
logic           ram_rlast;
DATA_TYPE       ram_rdata;

// Connect internal signal to external
assign rlast                      = rlast_int;
assign rvalid                     = rvalid_int;
assign wready                     = wready_int;

// Combinational signal
assign read_handshake             = rvalid_int && rready;
assign write_handshake            = wready_int && wvalid;
assign ram_read_handshake         = ram_rvalid && ram_rready;

// Almost signals
`GENERATE_START
if (ALMOST_FULL_LVL == FIFO_DEPTH) begin : alm_f_eq_depth
    assign walmost_full           = !wready_int;
end : alm_f_eq_depth
else begin : alm_f_lt_depth
    assign walmost_full           = (fifo_level > (ALMOST_FULL_LVL - 1));
end : alm_f_lt_depth
`GENERATE_END

`GENERATE_START
if (ALMOST_EMPTY_LVL == 0) begin : alm_e_eq_0
    assign ralmost_empty          = !rvalid_int;
end : alm_e_eq_0
else begin : alm_e_gt_0
    assign ralmost_empty          = (fifo_level < (ALMOST_EMPTY_LVL + 1));
end : alm_e_gt_0
`GENERATE_END

// Drop & peek signal
`GENERATE_START
if (EN_DROP_PACKET == BOOL_TRUE) begin : need_drop_sig
    assign need_drop              = wdrop;
end : need_drop_sig
else begin : no_drop_sig
    assign need_drop              = '0;
end : no_drop_sig
`GENERATE_END

`GENERATE_START
if (EN_PEEK_MODE == BOOL_TRUE) begin : need_peek_sig
    assign need_peek              = rpeek;
end : need_peek_sig
else begin : no_peek_sig
    assign need_peek              = '0;
end : no_peek_sig
`GENERATE_END

// FIFO level statistic
assign level                      = fifo_level;
assign wr_rd_addr_diff            = write_addr_next - read_addr_c_level;
assign fifo_level_next            = wr_rd_addr_diff[$bits(fifo_lvl_t) - 1:0] + (data_in_outff_next ? 1'd1 : 1'd0);

hs_unit_dff #(
    .DATA_TYPE  (fifo_lvl_t    ),
    .RESET_VALUE(fifo_lvl_t'(0))
) fifo_level_dff_inst
(
    .clk    (clk            ),
    .aresetn(aresetn        ),
    .din    (fifo_level_next),
    .dout   (fifo_level     )
);

// Transactions with LAST signal
assign pkt_last_write_trans       = write_handshake && wlast && !need_drop;
assign pkt_last_read_trans_nopeek = read_handshake && rlast_int && !need_peek;

hs_dpath_sfr #(
    .DATA_TYPE  (logic),
    .RESET_VALUE(1'b0 ),
    .LATENCY    (1    )
) pkt_last_write_trans_sfr_inst
(
    .clk    (clk                      ),
    .aresetn(aresetn                  ),
    .din    (pkt_last_write_trans     ),
    .dout   (pkt_last_write_trans_lat1)
);

// Output register data slice
// Note: If the output register enabled, the FIFO can store a data word into the output register.
`GENERATE_START
if (EN_OUTPUT_REG == BOOL_TRUE) begin : out_reg_flag
    always_comb begin : out_reg_flag_dete
        unique case ({ram_read_handshake, read_handshake})
            2'b00: data_in_outff_next = data_in_outff; // Nothing to do
            // One word is added on handshake on the input,
            // and no word is removed on handshake on the output
            2'b10: data_in_outff_next = 1'b1;          // Set to 1
            // No word is added on handshake on the input,
            // and one word is removed on handshake on the output
            2'b01: data_in_outff_next = 1'b0;          // Set to 0
            // One word is added on handshake on the input,
            // and one word is removed on handshake on the output
            2'b11: data_in_outff_next = data_in_outff; // Hold
        endcase
    end : out_reg_flag_dete

    hs_unit_dff #(
        .DATA_TYPE  (logic),
        .RESET_VALUE(1'b0 )
    ) data_in_outff_dff_inst
    (

        .clk    (clk               ),
        .aresetn(aresetn           ),
        .din    (data_in_outff_next),
        .dout   (data_in_outff     )
    );
end : out_reg_flag
else begin : no_out_reg_flag
    assign data_in_outff_next     = '0;
    assign data_in_outff          = '0;
end : no_out_reg_flag
`GENERATE_END

// Write address generate
assign write_addr_next_no_drop    = write_addr + (write_handshake ? 1'd1 : 1'd0);
assign write_addr_next            = need_drop ? write_addr_sop : write_addr_next_no_drop;

// Record the start of packet address for drop packet

`GENERATE_START
if (EN_DROP_PACKET == BOOL_TRUE) begin : gen_drop_pkt_addr
    hs_unit_dff_ce #(
        .DATA_TYPE  (fifo_addr_t    ),
        .RESET_VALUE(fifo_addr_t'(0))
    ) write_addr_sop_dff_inst
    (
        .clk    (clk                 ),
        .aresetn(aresetn             ),
        .ce     (pkt_last_write_trans),
        .din    (write_addr_next     ),
        .dout   (write_addr_sop      )
    );
end : gen_drop_pkt_addr
else begin : gen_no_drop_pkt_addr
    assign write_addr_sop         = '0;
end : gen_no_drop_pkt_addr
`GENERATE_END

// Write address register
hs_unit_dff #(
    .DATA_TYPE  (fifo_addr_t    ),
    .RESET_VALUE(fifo_addr_t'(0))
) write_addr_dff_inst
(
    .clk    (clk            ),
    .aresetn(aresetn        ),
    .din    (write_addr_next),
    .dout   (write_addr     )
);

// Read address generate
`GENERATE_START
if (EN_PEEK_MODE == BOOL_TRUE) begin : gen_raddr_peek
    always_comb begin : raddr_next_peek
        if (ram_rready && ram_rvalid) begin
            if (ram_rlast && rpeek) begin
                // Read the last data of packet but peek
                read_addr_next = read_addr;
            end
            else begin
                // Read the last data of packet but not peek
                read_addr_next = read_addr_peek + 'd1;
            end
        end
        else begin
            read_addr_next = read_addr_peek;
        end
    end : raddr_next_peek

    // Update read address register and peek address register
    hs_unit_dff #(
        .DATA_TYPE  (fifo_addr_t    ),
        .RESET_VALUE(fifo_addr_t'(0))
    ) read_addr_peek_dff_inst
    (
        .clk    (clk           ),
        .aresetn(aresetn       ),
        .din    (read_addr_next),
        .dout   (read_addr_peek)
    );


    hs_unit_dff_ce #(
        .DATA_TYPE  (fifo_addr_t    ),
        .RESET_VALUE(fifo_addr_t'(0))
    ) read_addr_dff_inst
    (
        .clk    (clk           ),
        .aresetn(aresetn       ),
        .ce     (!rpeek        ),
        .din    (read_addr_next),
        .dout   (read_addr     )
    );
end : gen_raddr_peek
else begin : gen_raddr_norm
    assign read_addr_next         = read_addr + (ram_read_handshake ? 1'd1 : 1'd0);
    assign read_addr_peek         = '0;

    // Update read address register
    hs_unit_dff #(
        .DATA_TYPE  (fifo_addr_t    ),
        .RESET_VALUE(fifo_addr_t'(0))
    ) read_addr_dff_inst
    (
        .clk    (clk           ),
        .aresetn(aresetn       ),
        .din    (read_addr_next),
        .dout   (read_addr     )
    );
end : gen_raddr_norm
`GENERATE_END

// Generate read address for calculating FIFO level
if (EN_PEEK_MODE == BOOL_TRUE) begin : gen_raddr_c_level_peek
    assign read_addr_c_level      = read_addr + ((ram_read_handshake && !rpeek) ? 1'd1 : 1'd0);
end : gen_raddr_c_level_peek
else begin : gen_raddr_c_level_nopk
    assign read_addr_c_level      = read_addr_next;
end : gen_raddr_c_level_nopk

// Read valid generate
assign ram_rvalid                 = ram_rvalid_req && (!full_pkt_est) && (!full_pkt_est_lat1);

`GENERATE_START
if (EN_PACKET_MODE == BOOL_TRUE) begin : gen_rvld_req_pkt
    if (EN_OUTPUT_REG == BOOL_TRUE) begin : rvld_req_pkt_outff
        hs_unit_dff #(.DATA_TYPE  (logic),
                       .RESET_VALUE(1'b0 )
        ) ram_rvalid_req_dff_inst
        (
            .clk    (clk               ),
            .aresetn(aresetn           ),
            .din    (|num_lasts_in_fifo),
            .dout   (ram_rvalid_req    )
        );
    end : rvld_req_pkt_outff
    else begin : rvld_req_pkt_no_outff
        hs_unit_dff #(.DATA_TYPE  (logic),
                       .RESET_VALUE(1'b0 )
        ) ram_rvalid_req_dff_inst
        (
            .clk    (clk                    ),
            .aresetn(aresetn                ),
            .din    (|num_lasts_in_fifo_next),
            .dout   (ram_rvalid_req         )
        );
    end : rvld_req_pkt_no_outff
end : gen_rvld_req_pkt
else begin : gen_rvld_req_nopkt
    hs_unit_dff #(
        .DATA_TYPE  (logic),
        .RESET_VALUE(1'b0 )
    ) ram_rvalid_req_dff_inst
    (
        .clk    (clk                         ),
        .aresetn(aresetn                     ),
        .din    (read_addr_next != write_addr),
        .dout   (ram_rvalid_req              )
    );
end : gen_rvld_req_nopkt
`GENERATE_END

// Full packet estimation for packet mode
`GENERATE_START
if ((EN_OUTPUT_REG == BOOL_TRUE) && (EN_PACKET_MODE == BOOL_TRUE)) begin : set_full_pkt_est
    // A pessimistic estimation of whether a full packet received
    // Including these saturations
    // 1. Full packet has been written to RAM
    // 2. Packet are parital in the RAM, and the output register has one word
    // 3. A packet which only have 1 word, and it's in the output register
    assign full_pkt_est           = pkt_last_read_trans_nopeek && (num_lasts_in_fifo <= 'd1);

    hs_dpath_sfr #
    (
        .DATA_TYPE  (logic),
        .RESET_VALUE(1'b0 ),
        .LATENCY    (1    )
    ) full_pkt_est_lat1_sfr_inst
    (
        .clk    (clk              ),
        .aresetn(aresetn          ),
        .din    (full_pkt_est     ),
        .dout   (full_pkt_est_lat1)
    );
end : set_full_pkt_est
else begin : no_pkt_mode_full_pkt_est
    assign full_pkt_est           = '0;
    assign full_pkt_est_lat1      = '0;
end : no_pkt_mode_full_pkt_est
`GENERATE_END

// Write ready logic
// NOTE: There is a functional difference only in the special case when the FIFO
// goes full in the same cycle as drop_packet is sent. In that case, wready will be low
// for one cycle and then go high the next.
// NOTE: There is a function difference when the FIFO is full and a read performed
// makes the FIFO ready for another write. In this case, wready will be low
// for one extra cycle after the read occurs, and then go high the next.
assign wready_next                = (read_addr[MEM_ADDR_WIDTH - 1:0] != write_addr_next_no_drop[MEM_ADDR_WIDTH - 1:0]) ||
 (read_addr[MEM_ADDR_WIDTH] == write_addr_next_no_drop[MEM_ADDR_WIDTH]) ||
 (ram_read_handshake && !need_peek);

hs_unit_dff #(
    .RESET_VALUE(1'b0 ),
    .DATA_TYPE  (logic)
)
wready_dff_inst (
    .clk    (clk        ),
    .aresetn(aresetn    ),
    .din    (wready_next),
    .dout   (wready_int )
);

// Packet mode: last signal in FIFO
`GENERATE_START
if (EN_PACKET_MODE == BOOL_TRUE) begin : gen_pkt_last_in_fifo
    hs_unit_dff #(
        .DATA_TYPE  (fifo_lvl_t    ),
        .RESET_VALUE(fifo_lvl_t'(0))
    ) pkt_last_in_fifo_dff_inst
    (
        .clk    (clk                   ),
        .aresetn(aresetn               ),
        .din    (num_lasts_in_fifo_next),
        .dout   (num_lasts_in_fifo     )
    );

    // Generate the next last statisitc
    // Note: A pipelined indicator has been used for the last cycle being written.
    // I.e. this is a pessimistic estimation for the number of packets that are in the FIFO.
    // This is so that valid write data always has time to propagate through the RAM
    // to the read side before this counter indicates that there is a packet available.
    // This is needed for packets that are one cycle long
    always_comb begin : pkt_last_in_fifo_dete
        unique case ({pkt_last_write_trans_lat1, pkt_last_read_trans_nopeek})
            2'b00: num_lasts_in_fifo_next = num_lasts_in_fifo;       // Nothing to do
            2'b01: num_lasts_in_fifo_next = num_lasts_in_fifo - 'd1; // Read out a LAST
            2'b10: num_lasts_in_fifo_next = num_lasts_in_fifo + 'd1; // Write in a LAST
            2'b11: num_lasts_in_fifo_next = num_lasts_in_fifo;       // Hold
        endcase
    end : pkt_last_in_fifo_dete
end : gen_pkt_last_in_fifo
else begin : gen_no_pkt_last_in_fifo
    assign num_lasts_in_fifo      = '0;
    assign num_lasts_in_fifo_next = '0;
end : gen_no_pkt_last_in_fifo
`GENERATE_END

// Memory block
assign ram_waddr                  = write_addr[MEM_ADDR_WIDTH - 1:0];
assign ram_raddr                  = read_addr_next[MEM_ADDR_WIDTH - 1:0];
assign ram_wen                    = wready_int && wvalid;

`GENERATE_START
if (EN_LAST_SIGNAL == BOOL_TRUE) begin : mem_w_last
    fifo_data_w_last_s ram_wdata_pkt;
    fifo_data_w_last_s ram_rdata_pkt;

    assign ram_wdata_pkt.data     = wdata;
    assign ram_wdata_pkt.tlast    = wlast;

    assign ram_rdata              = ram_rdata_pkt.data;
    assign ram_rlast              = ram_rdata_pkt.tlast;

    hs_mem_sdpram #(
        .DATA_TYPE (fifo_data_w_last_s),
        .DATA_DEPTH(MEM_ACT_DEPTH     )
    ) fifo_mem_inst
    (
        .clk  (clk          ),

        .waddr(ram_waddr    ),
        .wdata(ram_wdata_pkt),
        .wen  (ram_wen      ),

        .raddr(ram_raddr    ),
        .rdata(ram_rdata_pkt),
        .ren  (1'b1         )
    );
end : mem_w_last
else begin : mem_wo_last
    hs_mem_sdpram #(
        .DATA_TYPE (DATA_TYPE    ),
        .DATA_DEPTH(MEM_ACT_DEPTH)
    ) fifo_mem_inst
    (
        .clk  (clk      ),

        .waddr(ram_waddr),
        .wdata(wdata    ),
        .wen  (ram_wen  ),

        .raddr(ram_raddr),
        .rdata(ram_rdata),
        .ren  (1'b1     )
    );
end : mem_wo_last
`GENERATE_END

// Handshake pipeline for I/O
// Note: the pipeline data signal will only be added if
// the output register is enabled
hs_dpath_skid_buffer
#(
    .DATA_TYPE      (DATA_TYPE     ),
    .FULL_THROUGHPUT(BOOL_TRUE     ),
    .CTRL_PIPE      (BOOL_FALSE    ),
    .DATA_PIPE      (EN_OUTPUT_REG )
) skid_buffer_inst
(
    .clk       (clk       ),
    .aresetn   (aresetn   ),

    .in_data   (ram_rdata ),
    .in_valid  (ram_rvalid),
    .in_last   (ram_rlast ),
    .in_ready  (ram_rready),
    .in_strobe ('0        ),

    .out_data  (rdata     ),
    .out_valid (rvalid_int),
    .out_last  (rlast_int ),
    .out_ready (rready    ),
    .out_strobe(          )
);

endmodule : hs_fifo_sfifo