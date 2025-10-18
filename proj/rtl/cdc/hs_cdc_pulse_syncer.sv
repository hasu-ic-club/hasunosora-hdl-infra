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
// FILE NAME: hs_cdc_pulse_syncer.sv
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
// PURPOSE: Robust clock domain cross synchronizer for pulse signals
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME  RANGE           DESCRIPTION                   DEFAULT VALUE
// ACTIVE_LEVEL    level_e         Active pulse level to send    LEVEL_HIGH
//                 (Only HIGH/LOW)
// EN_FEEDBACK     bool_e          Enable feedback path to avoid BOOL_ENABLE
//                                 pulse overload
// SYNC_STAGE      2-32            Series stage count of the     2
//                                 synchronizer
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// Robust clock domain cross synchronizer for pulse signals
module hs_cdc_pulse_syncer
import hs_ifr_misc_typedefs_pkg::*;
#(
    parameter level_e ACTIVE_LEVEL = LEVEL_HIGH,
    parameter bool_e  EN_FEEDBACK  = BOOL_TRUE,
    parameter int     SYNC_STAGE   = 2
)
(
    // Source side
    input  logic src_clk,
    input  logic src_aresetn,
    input  logic pulse_in,
    input  logic overload_sclr,
    output logic fb_overload,

    // Destination side
    input  logic dst_clk,
    input  logic dst_aresetn,
    output logic pulse_out
);

logic expected_pulse;
logic pulse_valid;

logic pulse_lvl;
logic pulse_lvl_synced_dst;
logic pulse_lvl_fb_synced_src;
logic src_dst_lvl_equal;

logic dst_pulse_lvl;

// Expected pulse level
`GENERATE_START
if (ACTIVE_LEVEL == LEVEL_HIGH) begin : exp_lvl_high
    assign expected_pulse          = 1'b1;
end : exp_lvl_high
else begin : exp_lvl_low
    assign expected_pulse          = 1'b0;
end : exp_lvl_low
`GENERATE_END

assign pulse_valid       = (pulse_in == expected_pulse);

// Pulse to level changed
hs_unit_dff_ce #(
    .RESET_VALUE(1'b0 ),
    .DATA_TYPE  (logic)
)
pulse_lvl_dff_inst (
    .clk    (src_clk    ),
    .aresetn(src_aresetn),
    .ce     (pulse_valid),
    .din    (~pulse_lvl ),
    .dout   (pulse_lvl  )
);

// Level changed monitor
hs_unit_dff #(
    .RESET_VALUE(1'b0 ),
    .DATA_TYPE  (logic)
)
dst_pulse_lvl_dff_inst (
    .clk    (dst_clk             ),
    .aresetn(dst_aresetn         ),
    .din    (pulse_lvl_synced_dst),
    .dout   (dst_pulse_lvl       )
);

// Overload detector (only valid when feedback enabled)
`GENERATE_START
if (EN_FEEDBACK == BOOL_TRUE) begin : en_fb_ovld_det
    assign src_dst_lvl_equal       = pulse_lvl_fb_synced_src == pulse_lvl;
end : en_fb_ovld_det
else begin : no_ovld_det
    assign src_dst_lvl_equal       = 1'b0;
end : no_ovld_det
`GENERATE_END

hs_unit_dff_ce_sclr #(
    .RESET_VALUE(1'b0 ),
    .DATA_TYPE  (logic)
)
overload_dff_inst (
    .clk    (src_clk          ),
    .aresetn(src_aresetn      ),
    .sclr   (overload_sclr    ),
    .ce     (src_dst_lvl_equal),
    .din    (1'b1             ),
    .dout   (fb_overload      )
);

// Output pulse generate
`GENERATE_START
if (ACTIVE_LEVEL == LEVEL_HIGH) begin : act_lvl_high
    assign pulse_out               = dst_pulse_lvl ^ pulse_lvl_synced_dst;
end : act_lvl_high
else begin : act_lvl_low
    assign pulse_out               = !(dst_pulse_lvl ^ pulse_lvl_synced_dst);
end : act_lvl_low
`GENERATE_END

// Cross domain
hs_cdc_syncer #(
    .SYNC_STAGE(SYNC_STAGE)
)
pulse_lvl_cvt_syncer_inst (
    .clk    (dst_clk             ),
    .aresetn(dst_aresetn         ),
    .din    (pulse_lvl           ),
    .dout   (pulse_lvl_synced_dst)
);

`GENERATE_START
if (EN_FEEDBACK == BOOL_TRUE) begin : en_feedback_cdc
    hs_cdc_syncer #(
        .SYNC_STAGE(SYNC_STAGE)
    )
    feedback_syncer_inst (
        .clk    (src_clk                ),
        .aresetn(src_aresetn            ),
        .din    (pulse_lvl_synced_dst   ),
        .dout   (pulse_lvl_fb_synced_src)
    );
end : en_feedback_cdc
else begin : no_feedback_cdc
    assign pulse_lvl_fb_synced_src = '0;
end : no_feedback_cdc
`GENERATE_END

endmodule : hs_cdc_pulse_syncer