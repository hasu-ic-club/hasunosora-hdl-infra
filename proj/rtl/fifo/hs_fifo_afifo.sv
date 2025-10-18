//+FHDR--------------------------------------------------------------------
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
//-------------------------------------------------------------------------
// FILE NAME: hs_fifo_afifo.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a0
// VERSION DESCRIPTION: First Edition
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/9/26     First Edition
//-------------------------------------------------------------------------
// PURPOSE: Parameterized Asynchronous FIFO
//          This design referenced the design in 
//                https://github.com/hdl-modules/hdl-modules. 
//          I translated the VHDL to SystemVerilog and modify some comments 
//          and design implementations. I respect and must thank contributors 
//          of hdl-modules, who provides so beautiful and reliable design in VHDL, 
//          that I can learn many things from it. 
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE          DESCRIPTION                   DEFAULT VALUE
// DATA_TYPE           type           Type of data in FIFO          logic
// SYNC_STAGE          2-32           Series stage count of the     2
//                                    synchronizer
// FIFO_DEPTH          2-16777216     Maximum depth of the FIFO     16
// ALMOST_FULL_LVL     0-FIFO_DEPTH   Level to show 'almost full'   FIFO_DEPTH
// ALMOST_EMPTY_LVL    0-FIFO_DEPTH   Level to show 'almost empty'  0
// EN_LAST_SIGNAL      bool_e         If true, user can use 'last'  BOOL_FALSE
//                                    signals
// EN_PACKET_MODE      bool_e         If true, 'rvalid' will        BOOL_FALSE
//                                    not be asserted until a full
//                                    packet is available in FIFO
// EN_DROP_PACKET      bool_e         If true, user can use 'wdrop' BOOL_FALSE
//                                    port
// EN_PEEK_MODE        bool_e         If true, use can read words
//                                    w/o popping from FIFO by use  BOOL_FALSE
//                                    the 'rpeek' port
// EN_OUTPUT_REG       bool_e         Use an extra output register  BOOL_FALSE
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// Parameterized Asynchronous FIFO
module hs_fifo_afifo
import hs_ifr_misc_typedefs_pkg::*;
#(
    parameter type   DATA_TYPE        = logic,
    parameter int    SYNC_STAGE       = 2,
    parameter int    FIFO_DEPTH       = 16,
    parameter int    ALMOST_FULL_LVL  = FIFO_DEPTH,
    parameter int    ALMOST_EMPTY_LVL = 0,
    parameter bool_e EN_LAST_SIGNAL   = BOOL_FALSE,
    parameter bool_e EN_PACKET_MODE   = BOOL_FALSE,
    parameter bool_e EN_DROP_PACKET   = BOOL_FALSE,
    parameter bool_e EN_OUTPUT_REG    = BOOL_FALSE,
    `LP_MODULE int   FIFO_LEVEL_WIDTH = $clog2(FIFO_DEPTH + 1)
)
(
    // Source (Write) clock domain
    input  logic                              src_clk,
    input  logic                              src_aresetn,

    // Destination (Read) clock domain
    input  logic                              dst_clk,
    input  logic                              dst_aresetn,

    // Write side (synchronized with src_clk)
    input  logic                              wvalid,
    output logic                              wready,
    input  DATA_TYPE                          wdata,
    input  logic                              wlast,
    input  logic                              wdrop,
    output logic                              walmost_full,
    output logic     [FIFO_LEVEL_WIDTH - 1:0] wlevel,

    // Read side (synchronized with dst_clk)
    output logic                              rvalid,
    input  logic                              rready,
    output DATA_TYPE                          rdata,
    output logic                              rlast,
    output logic                              ralmost_empty,
    output logic     [FIFO_LEVEL_WIDTH - 1:0] rlevel         // NOTE: Unsupported under Packet Mode (always 0)
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
    initial $fatal(1, "Must enable Packet Mode to enable Drop Packet.");
end : assert_drop_pkt_mode

if ((EN_PACKET_MODE == BOOL_TRUE) && (ALMOST_EMPTY_LVL != 0)) begin : assert_no_alm_supp_pkt_mode
    initial $fatal(1, "The setting of Almost Empty Level is not supported when enable Packet Mode." +
            "Also, the Read Level signal is not supported under this mode too.");
end : assert_no_alm_supp_pkt_mode
`GENERATE_END

localparam  int MEM_ACT_DEPTH                  = FIFO_DEPTH - ((EN_OUTPUT_REG == hs_ifr_misc_typedefs_pkg::BOOL_TRUE) ? 1 : 0);
localparam  int MEM_ADDR_WIDTH                 = $clog2(MEM_ACT_DEPTH);
localparam  int MEM_ADDR_EXTEND                = MEM_ADDR_WIDTH + 1;

// The FIFO level number needs to be in range [0, FIFO_DEPTH]
typedef logic [FIFO_LEVEL_WIDTH - 1:0] fifo_lvl_t;
// Extra bits in the addresses to be able to make the distinction if the FIFO is full/empty
typedef logic [MEM_ADDR_EXTEND - 1:0]  fifo_addr_t;
// The part of the address that actually goes to the RAM
typedef logic [MEM_ADDR_WIDTH - 1:0]   mem_addr_t;

// Data packet with last signal
typedef struct packed
{
    logic     tlast;
    DATA_TYPE data;
} fifo_data_w_last_s;

// FIFO level
fifo_lvl_t      fifo_wlevel;
fifo_lvl_t      fifo_wlevel_next;
fifo_lvl_t      fifo_rlevel;
fifo_lvl_t      fifo_rlevel_next;
fifo_lvl_t      fifo_rlevel_est_next;
fifo_addr_t     wr_sync_rd_addr_diff;
fifo_addr_t     wr_rd_addr_sync_diff;

// Flag to indicate there is a word in output register
logic           data_in_outff;
logic           data_in_outff_next;

// Read addresses
fifo_addr_t     read_addr_next;
fifo_addr_t     read_addr;

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

// Packet flags
fifo_lvl_t      num_pkt_in_fifo;
fifo_lvl_t      num_pkt_in_fifo_next;
fifo_lvl_t      num_pkt_written;
fifo_lvl_t      num_pkt_written_next;
fifo_lvl_t      num_pkt_read;
fifo_lvl_t      num_pkt_read_next;

logic           full_pkt_est;
logic           full_pkt_est_lat1;

// Drop signal
logic           need_drop;

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
logic           ram_rvalid_req_next;
logic           ram_rready;
logic           ram_rvalid;
logic           ram_rlast;
DATA_TYPE       ram_rdata;

// Resynchronized addresses
fifo_addr_t     write_addr_resync;
fifo_addr_t     read_addr_resync;
fifo_lvl_t      num_pkt_written_resync;

// Connect internal signal to external
assign rlast                   = rlast_int;
assign rvalid                  = rvalid_int;
assign wready                  = wready_int;


// Combinational signal
assign read_handshake          = rvalid_int && rready;
assign write_handshake         = wready_int && wvalid;
assign ram_read_handshake      = ram_rvalid && ram_rready;

// Almost signals
`GENERATE_START
if (ALMOST_FULL_LVL == FIFO_DEPTH) begin : alm_f_eq_depth
    assign walmost_full           = !wready_int;
end : alm_f_eq_depth
else begin : alm_f_lt_depth
    assign walmost_full           = (fifo_wlevel > (ALMOST_FULL_LVL - 1));
end : alm_f_lt_depth
`GENERATE_END

`GENERATE_START
if (ALMOST_EMPTY_LVL == 0) begin : alm_e_eq_0
    assign ralmost_empty          = !rvalid_int;
end : alm_e_eq_0
else begin : alm_e_gt_0
    assign ralmost_empty          = (fifo_rlevel < (ALMOST_EMPTY_LVL + 1));
end : alm_e_gt_0
`GENERATE_END

// Drop signal
`GENERATE_START
if (EN_DROP_PACKET == BOOL_TRUE) begin : need_drop_sig
    assign need_drop              = wdrop;
end : need_drop_sig
else begin : no_drop_sig
    assign need_drop              = '0;
end : no_drop_sig
`GENERATE_END

// Write side FIFO level
assign wlevel                  = fifo_wlevel;
assign wr_rd_addr_sync_diff    = write_addr - read_addr_resync;

`GENERATE_START
if (EN_OUTPUT_REG == BOOL_TRUE) begin : en_outff_wrlvl
    assign fifo_wlevel_next       = wr_rd_addr_sync_diff[$bits(fifo_lvl_t) - 1:0] + 'd1;

    hs_unit_dff #(
        .DATA_TYPE  (fifo_lvl_t    ),
        .RESET_VALUE(fifo_lvl_t'(1))
    ) fifo_wlevel_dff_inst
    (
        .clk    (src_clk         ),
        .aresetn(src_aresetn     ),
        .din    (fifo_wlevel_next),
        .dout   (fifo_wlevel     )
    );
end : en_outff_wrlvl
else begin : dis_outff_wrlvl
    assign fifo_wlevel_next       = wr_rd_addr_sync_diff[$bits(fifo_lvl_t) - 1:0];

    hs_unit_dff #(
        .DATA_TYPE  (fifo_lvl_t    ),
        .RESET_VALUE(fifo_lvl_t'(0))
    ) fifo_wlevel_dff_inst
    (
        .clk    (src_clk         ),
        .aresetn(src_aresetn     ),
        .din    (fifo_wlevel_next),
        .dout   (fifo_wlevel     )
    );
end : dis_outff_wrlvl
`GENERATE_END

// Read side FIFO level
assign rlevel                  = fifo_rlevel;

`GENERATE_START
if (EN_PACKET_MODE == BOOL_FALSE) begin : rlvl_no_pkt_mode
    assign wr_sync_rd_addr_diff   = write_addr_resync - read_addr_next;
    assign fifo_rlevel_next       = wr_sync_rd_addr_diff[$bits(fifo_lvl_t) - 1:0];
    assign fifo_rlevel_est_next   = fifo_rlevel_next + (data_in_outff_next ? 1'd1 : 1'd0);

    hs_unit_dff #(
        .DATA_TYPE  (fifo_lvl_t    ),
        .RESET_VALUE(fifo_lvl_t'(0))
    ) fifo_rlevel_dff_inst
    (
        .clk    (dst_clk             ),
        .aresetn(dst_aresetn         ),
        .din    (fifo_rlevel_est_next),
        .dout   (fifo_rlevel         )
    );
end : rlvl_no_pkt_mode
else begin : rlvl_no_supp
    assign wr_sync_rd_addr_diff   = '0;
    assign fifo_rlevel            = '0;
    assign fifo_rlevel_next       = '0;
    assign fifo_rlevel_est_next   = '0;
end : rlvl_no_supp
`GENERATE_END

// Output register data slice
// NOTE: If the output register enabled, the FIFO can store a data word into the output register.
// NOTE: When packet mode is enabled, we do not track the number of words in the output register.
`GENERATE_START
if ((EN_PACKET_MODE == BOOL_FALSE) && (EN_OUTPUT_REG == BOOL_TRUE)) begin : out_reg_flag
    always_comb begin : out_reg_flag_dete
        unique case ({ram_read_handshake, read_handshake})
            2'b00: data_in_outff_next = data_in_outff;   // Nothing to do
            // One word is added on handshake on the input,
            // and no word is removed on handshake on the output
            2'b10: data_in_outff_next = 1'b1;            // Set to 1
            // No word is added on handshake on the input,
            // and one word is removed on handshake on the output
            2'b01: data_in_outff_next = 1'b0;            // Set to 0
            // One word is added on handshake on the input,
            // and one word is removed on handshake on the output
            2'b11: data_in_outff_next = data_in_outff;   // Hold
        endcase
    end : out_reg_flag_dete

    hs_unit_dff #(
        .DATA_TYPE  (logic),
        .RESET_VALUE(1'b0 )
    ) data_in_outff_dff_inst
    (

        .clk    (dst_clk           ),
        .aresetn(dst_aresetn       ),
        .din    (data_in_outff_next),
        .dout   (data_in_outff     )
    );
end : out_reg_flag
else begin  : no_out_reg_flag
    assign data_in_outff_next     = '0;
    assign data_in_outff          = '0;
end : no_out_reg_flag
`GENERATE_END

// Write address generate
assign write_addr_next_no_drop = write_addr + (write_handshake ? 1'd1 : 1'd0);
assign write_addr_next         = need_drop ? write_addr_sop : write_addr_next_no_drop;

// Record the start of packet address for drop packet
`GENERATE_START
if (EN_DROP_PACKET == hs_ifr_misc_typedefs_pkg::BOOL_TRUE) begin : gen_drop_pkt_addr
    hs_unit_dff_ce #(
        .DATA_TYPE  (fifo_addr_t    ),
        .RESET_VALUE(fifo_addr_t'(0))
    ) write_addr_sop_dff_inst
    (
        .clk    (src_clk                               ),
        .aresetn(src_aresetn                           ),
        .ce     (write_handshake && wlast && !need_drop),
        .din    (write_addr_next                       ),
        .dout   (write_addr_sop                        )
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
    .clk    (src_clk        ),
    .aresetn(src_aresetn    ),
    .din    (write_addr_next),
    .dout   (write_addr     )
);

// Read address generate
assign read_addr_next          = read_addr + (ram_read_handshake ? 1'd1 : 1'd0);

hs_unit_dff #(
    .DATA_TYPE  (fifo_addr_t    ),
    .RESET_VALUE(fifo_addr_t'(0))
) read_addr_dff_inst
(
    .clk    (dst_clk       ),
    .aresetn(dst_aresetn   ),
    .din    (read_addr_next),
    .dout   (read_addr     )
);

// Read valid generate
assign ram_rvalid              = ram_rvalid_req && (!full_pkt_est) && (!full_pkt_est_lat1);

`GENERATE_START
if (EN_PACKET_MODE == BOOL_TRUE) begin : gen_rvld_req_pkt
    if (EN_OUTPUT_REG == BOOL_TRUE) begin : rvld_req_pkt_outff
        assign ram_rvalid_req_next = num_pkt_read != num_pkt_written_resync;
    end : rvld_req_pkt_outff
    else begin : rvld_req_pkt_no_outff
        assign ram_rvalid_req_next = num_pkt_read_next != num_pkt_written_resync;
    end : rvld_req_pkt_no_outff
end : gen_rvld_req_pkt
else begin : gen_rvld_req_nopkt
    assign ram_rvalid_req_next    = |fifo_rlevel_next;
end : gen_rvld_req_nopkt
`GENERATE_END

hs_unit_dff #(
    .DATA_TYPE  (logic),
    .RESET_VALUE(1'b0 )
) ram_rvalid_req_dff_inst
(
    .clk    (dst_clk            ),
    .aresetn(dst_aresetn        ),
    .din    (ram_rvalid_req_next),
    .dout   (ram_rvalid_req     )
);

// Read side statistic number of packets in FIFO
if ((EN_PACKET_MODE == BOOL_TRUE) && (EN_OUTPUT_REG == BOOL_TRUE)) begin : en_stat_pkt_in_fifo
    assign num_pkt_in_fifo_next   = num_pkt_written_resync - num_pkt_read_next;
    assign full_pkt_est           = read_handshake && rlast_int && (num_pkt_in_fifo <= 'd1);

    hs_unit_dff #(
        .DATA_TYPE  (fifo_lvl_t    ),
        .RESET_VALUE(fifo_lvl_t'(0))
    ) num_pkt_in_fifo_dff_inst
    (
        .clk    (dst_clk             ),
        .aresetn(dst_aresetn         ),
        .din    (num_pkt_in_fifo_next),
        .dout   (num_pkt_in_fifo     )
    );

    hs_dpath_sfr #
    (
        .DATA_TYPE  (logic),
        .RESET_VALUE(1'b0 ),
        .LATENCY    (1    )
    ) full_pkt_est_lat1_sfr_inst
    (
        .clk    (dst_clk          ),
        .aresetn(dst_aresetn      ),
        .din    (full_pkt_est     ),
        .dout   (full_pkt_est_lat1)
    );
end : en_stat_pkt_in_fifo
else begin : dis_stat_pkt_in_fifo
    assign num_pkt_in_fifo        = '0;
    assign num_pkt_in_fifo_next   = '0;
    assign full_pkt_est           = '0;
    assign full_pkt_est_lat1      = '0;
end : dis_stat_pkt_in_fifo

// Write ready logic
assign wready_next             = (read_addr_resync[MEM_ADDR_WIDTH - 1:0] != write_addr_next_no_drop[MEM_ADDR_WIDTH - 1:0]) ||
    (read_addr_resync[MEM_ADDR_WIDTH] == write_addr_next_no_drop[MEM_ADDR_WIDTH]);

hs_unit_dff #(
    .RESET_VALUE(1'b0 ),
    .DATA_TYPE  (logic)
)
wready_dff_inst (
    .clk    (src_clk    ),
    .aresetn(src_aresetn),
    .din    (wready_next),
    .dout   (wready_int )
);

// Statistic packet written to FIFO (only packet mode)
`GENERATE_START
if (EN_PACKET_MODE == BOOL_TRUE) begin : en_stat_pkt_wr
    assign num_pkt_written_next   = num_pkt_written +
        ((write_handshake && wlast && !need_drop) ? 1'd1 : 1'd0);

    hs_unit_dff #(
        .DATA_TYPE  (fifo_lvl_t    ),
        .RESET_VALUE(fifo_lvl_t'(0))
    ) num_pkt_written_dff_inst
    (
        .clk    (src_clk             ),
        .aresetn(src_aresetn         ),
        .din    (num_pkt_written_next),
        .dout   (num_pkt_written     )
    );
end : en_stat_pkt_wr
else begin : dis_stat_pkt_wr
    assign num_pkt_written        = '0;
    assign num_pkt_written_next   = '0;
end : dis_stat_pkt_wr
`GENERATE_END

// Statistic packet read from FIFO (only packet mode)

`GENERATE_START
if (EN_PACKET_MODE == BOOL_TRUE) begin : en_stat_pkt_rd
    assign num_pkt_read_next      = num_pkt_read +
        ((read_handshake && rlast_int) ? 1'd1 : 1'd0);

    hs_unit_dff #(
        .DATA_TYPE  (fifo_lvl_t    ),
        .RESET_VALUE(fifo_lvl_t'(0))
    ) num_pkt_read_dff_inst
    (
        .clk    (dst_clk          ),
        .aresetn(dst_aresetn      ),
        .din    (num_pkt_read_next),
        .dout   (num_pkt_read     )
    );
end : en_stat_pkt_rd
else begin : dis_stat_pkt_rd
    assign num_pkt_read           = '0;
    assign num_pkt_read_next      = '0;
end : dis_stat_pkt_rd
`GENERATE_END

// Clock domain cross (resynchronization)
hs_cdc_syncer_gray #(
    .SYNC_STAGE(SYNC_STAGE      ),
    .WIDTH     ($bits(read_addr))
)
read_addr_cdc
(
    .clk    (src_clk         ),
    .aresetn(src_aresetn     ),
    .din    (read_addr_next  ),
    .dout   (read_addr_resync)
);

`GENERATE_START
if (EN_PACKET_MODE == BOOL_FALSE) begin : en_cdc_addr_wr
    hs_cdc_syncer_gray #(
        .SYNC_STAGE(SYNC_STAGE       ),
        .WIDTH     ($bits(write_addr))
    )
    write_addr_cdc
    (
        .clk    (dst_clk          ),
        .aresetn(dst_aresetn      ),
        .din    (write_addr       ),
        .dout   (write_addr_resync)
    );

    assign num_pkt_written_resync = '0;
end : en_cdc_addr_wr
else begin : en_cdc_num_pkt_wr
    // The write address is not used in read side in packet mode
    // We use the number of packet written instead of it

    hs_cdc_syncer_gray #(
        .SYNC_STAGE(SYNC_STAGE            ),
        .WIDTH     ($bits(num_pkt_written))
    )
    num_pkt_written_cdc
    (
        .clk    (dst_clk               ),
        .aresetn(dst_aresetn           ),
        .din    (num_pkt_written       ),
        .dout   (num_pkt_written_resync)
    );

    assign write_addr_resync      = '0;
end : en_cdc_num_pkt_wr
`GENERATE_END

// Memory block
assign ram_waddr               = write_addr[MEM_ADDR_WIDTH - 1:0];
assign ram_raddr               = read_addr_next[MEM_ADDR_WIDTH - 1:0];
assign ram_wen                 = wready_int && wvalid;

`GENERATE_START
if (EN_LAST_SIGNAL == BOOL_TRUE) begin : mem_w_last
    fifo_data_w_last_s ram_wdata_pkt;
    fifo_data_w_last_s ram_rdata_pkt;

    assign ram_wdata_pkt.data     = wdata;
    assign ram_wdata_pkt.tlast    = wlast;

    assign ram_rdata              = ram_rdata_pkt.data;
    assign ram_rlast              = ram_rdata_pkt.tlast;

    hs_mem_sdpram_2clk #(
        .DATA_DEPTH(MEM_ACT_DEPTH     ),
        .DATA_TYPE (fifo_data_w_last_s)
    )
    fifo_mem_inst
    (
        .wclk (src_clk      ),
        .rclk (dst_clk      ),
        .waddr(ram_waddr    ),
        .wdata(ram_wdata_pkt),
        .wen  (ram_wen      ),
        .raddr(ram_raddr    ),
        .ren  (1'b1         ),
        .rdata(ram_rdata_pkt)
    );
end : mem_w_last
else begin : mem_wo_last
    hs_mem_sdpram_2clk #(
        .DATA_DEPTH(MEM_ACT_DEPTH),
        .DATA_TYPE (DATA_TYPE    )
    )
    fifo_mem_inst
    (
        .wclk (src_clk  ),
        .rclk (dst_clk  ),
        .waddr(ram_waddr),
        .wdata(wdata    ),
        .wen  (ram_wen  ),
        .raddr(ram_raddr),
        .ren  (1'b1     ),
        .rdata(ram_rdata)
    );
end : mem_wo_last
`GENERATE_END

// Handshake pipeline for I/O
// Note: the pipeline data signal will only be added if
//       the output register is enabled
hs_dpath_skid_buffer
#(
    .DATA_TYPE      (DATA_TYPE    ),
    .FULL_THROUGHPUT(BOOL_TRUE    ),
    .CTRL_PIPE      (BOOL_FALSE   ),
    .DATA_PIPE      (EN_OUTPUT_REG)
) skid_buffer_inst
(
    .clk       (dst_clk    ),
    .aresetn   (dst_aresetn),

    .in_data   (ram_rdata  ),
    .in_valid  (ram_rvalid ),
    .in_last   (ram_rlast  ),
    .in_ready  (ram_rready ),
    .in_strobe ('0         ),

    .out_data  (rdata      ),
    .out_valid (rvalid_int ),
    .out_last  (rlast_int  ),
    .out_ready (rready     ),
    .out_strobe(           )
);

endmodule : hs_fifo_afifo