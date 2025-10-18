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
// FILE NAME: hs_cdc_2phase_handshake.sv
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
// PURPOSE: 2-Phase clock domain cross for multi-bit data with handshake control
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE              DESCRIPTION                 DEFAULT VALUE
// DATA_TYPE           type               Type of data to cross domain logic
// RESET_DATA_PATH     bool_e             Enable reset on data-path    BOOL_FALSE
// RESET_VALUE         Range of DATA_TYPE Value when DFF reset         1'b0
// SYNC_STAGE          2-32               Series stage count of the    2
//                                        synchronizer
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// 2-Phase clock domain cross for multi-bit data with handshake control
module hs_cdc_2phase_handshake
import hs_ifr_misc_typedefs_pkg::*;
#(
    parameter type      DATA_TYPE       = logic,
    parameter bool_e    RESET_DATA_PATH = BOOL_FALSE,
    parameter DATA_TYPE RESET_VALUE     = 1'b0,
    parameter int       SYNC_STAGE      = 2
)
(
    // Source domain
    input  logic     src_clk,
    input  logic     src_aresetn,
    input  DATA_TYPE src_data,
    input  logic     src_valid,
    output logic     src_ready,

    // Destination domain
    input  logic     dst_clk,
    input  logic     dst_aresetn,
    output DATA_TYPE dst_data,
    output logic     dst_valid,
    input  logic     dst_ready
);

`ASYNC_REG_HINT DATA_TYPE src_reg;
`ASYNC_REG_HINT DATA_TYPE dst_reg;

logic dst_valid_int;
logic dst_handshake;

logic src_2phase_reg;
logic dst_2phase_reg;
logic dst_handshake_lvl;

logic src_2phase_synced_dst;
logic dst_2phase_synced_src;

logic src_reg_we;
logic dst_reg_we;

// Combintional signal
assign dst_handshake = dst_valid_int && dst_ready;

if (RESET_DATA_PATH == BOOL_TRUE) begin : gen_reset_data_path
    // Synchronous DFFs
    always_ff @(posedge src_clk, negedge src_aresetn) begin : src_dff
        if (!src_aresetn)    src_reg <= RESET_VALUE;
        else if (src_reg_we) src_reg <= src_data;
    end : src_dff

    // Asynchronous DFFs
    always_ff @(posedge dst_clk, negedge dst_aresetn) begin : dst_dff
        if (!dst_aresetn)    dst_reg <= RESET_VALUE;
        else if (dst_reg_we) dst_reg <= src_reg;        // This is the CDC path
    end : dst_dff
end : gen_reset_data_path
else begin : gen_no_reset_data_path
    // Synchronous DFFs
    always_ff @(posedge src_clk) begin : src_dff
        if (src_reg_we) src_reg <= src_data;
    end : src_dff

    // Asynchronous DFFs
    always_ff @(posedge dst_clk) begin : dst_dff
        if (dst_reg_we) dst_reg <= src_reg;        // This is the CDC path
    end : dst_dff
end

// Write enable generate
assign src_reg_we    = src_2phase_reg ^ dst_2phase_synced_src;
assign dst_reg_we    = (dst_handshake_lvl ^ src_2phase_synced_dst) && !dst_valid_int;

// Handshake signal generate
assign src_ready     = src_reg_we;

// CDC
hs_cdc_syncer #(
    .SYNC_STAGE(SYNC_STAGE)
)
src_2_dst_syncer_inst
(
    .clk    (dst_clk              ),
    .aresetn(dst_aresetn          ),
    .din    (src_2phase_reg       ),
    .dout   (src_2phase_synced_dst)
);


hs_cdc_syncer #(
    .SYNC_STAGE(SYNC_STAGE)
)
dst_2_src_syncer_inst
(
    .clk    (src_clk              ),
    .aresetn(src_aresetn          ),
    .din    (dst_2phase_reg       ),
    .dout   (dst_2phase_synced_src)
);

// Output handshake DFFs

// The output valid register
// We need to set it to 1 when we update a new data into the output register
// And, after handshaked, we need to de-assert this signal
hs_unit_dff_ce #(
    .RESET_VALUE(1'b0 ),
    .DATA_TYPE  (logic)
)
dst_valid_reg_inst
(
    .clk    (dst_clk                    ),
    .aresetn(dst_aresetn                ),
    .ce     (dst_reg_we || dst_handshake), // new data || handshake
    .din    (dst_reg_we                 ), // 1 when new data, 0 when handshake
    .dout   (dst_valid_int              )
);


hs_unit_dff_ce #(
    .RESET_VALUE(1'b0 ),
    .DATA_TYPE  (logic)
)
dst_handshake_lvl_reg_inst
(
    .clk    (dst_clk           ),
    .aresetn(dst_aresetn       ),
    .ce     (dst_handshake     ),
    .din    (~dst_handshake_lvl),
    .dout   (dst_handshake_lvl )
);

// 2-phase registers
hs_unit_dff_ce #(
    .RESET_VALUE(1'b0 ),
    .DATA_TYPE  (logic)
)
src_2phase_reg_inst
(
    .clk    (src_clk              ),
    .aresetn(src_aresetn          ),
    .ce     (src_valid            ),
    .din    (dst_2phase_synced_src),
    .dout   (src_2phase_reg       )
);

hs_unit_dff_ce #(
    .RESET_VALUE(1'b1 ), // This is important
    .DATA_TYPE  (logic)
)
dst_2phase_reg_inst
(
    .clk    (dst_clk        ),
    .aresetn(dst_aresetn    ),
    .ce     (dst_reg_we     ),
    .din    (~dst_2phase_reg),
    .dout   (dst_2phase_reg )
);

// Output
assign dst_data      = dst_reg;
assign dst_valid     = dst_valid_int;

endmodule : hs_cdc_2phase_handshake