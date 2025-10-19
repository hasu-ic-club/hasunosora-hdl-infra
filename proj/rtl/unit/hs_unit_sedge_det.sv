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
// FILE NAME: hs_unit_sedge_det.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-----------------------------------------------------------------------
// RELEASE VERSION:     0.1a0
// VERSION DESCRIPTION: Initial version
//-----------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/09       Initial version
//-----------------------------------------------------------------------
// PURPOSE:
//  Synchronized Edge Detector
//-----------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME    RANGE         DESCRIPTION            DEFAULT VALUE
//-----------------------------------------------------------------------
// EDGE              edge_e        Which edge should be   hs_ifr_misc_typedefs_pkg::EDGE_POSEDGE
//                                 detected out
//-FHDR------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE

// Synchronized Edge Detector
module hs_unit_sedge_det
    import hs_ifr_misc_typedefs_pkg::edge_e;
#(
    parameter edge_e EDGE = hs_ifr_misc_typedefs_pkg::EDGE_POSEDGE
)
(
    // Clock & reset
    input  logic clk,
    input  logic aresetn,

    // Signal input
    input  logic signal_in,

    // Edge output
    output logic edge_dete
);

logic sig_dly_1cycle;

hs_dpath_sfr #(
    .RESET_VALUE(1'b0 ),
    .LATENCY    (1    ),
    .DATA_TYPE  (logic)
)
lat1_sfr_inst (
    .clk    (clk           ),
    .aresetn(aresetn       ),
    .din    (signal_in     ),
    .dout   (sig_dly_1cycle)
);

`GENERATE_START
if (EDGE == hs_ifr_misc_typedefs_pkg::EDGE_POSEDGE) begin : posedge_dete
    assign edge_dete = (~sig_dly_1cycle) & signal_in;
end : posedge_dete
else if (EDGE == hs_ifr_misc_typedefs_pkg::EDGE_NEGEDGE) begin : negedge_dete
    assign edge_dete = sig_dly_1cycle & (~signal_in);
end : negedge_dete
else begin : both_dete
    assign edge_dete = sig_dly_1cycle ^ signal_in;
end : both_dete
`GENERATE_END

endmodule : hs_unit_sedge_det
