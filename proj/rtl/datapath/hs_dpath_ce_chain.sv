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
// FILE NAME: hs_dpath_ce_chain.sv
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
//  Paramaterized shift register (SFR) for CE chain
//-----------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME    RANGE         DESCRIPTION            DEFAULT VALUE
//-----------------------------------------------------------------------
// LATENCY           1:4294967295  The data latency from  1
//                                 input to output
//-FHDR------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// Paramaterized shift register (SFR) for CE chain
module hs_dpath_ce_chain
#(
    parameter int LATENCY = 1
)
(
    // Clock & reset
    input  logic clk,
    input  logic aresetn,

    // Input
    input  logic ce,

    // Output
    output logic ce_out  [LATENCY + 1]  // [0] = CE in, [1:LATENCY] = CE chain tapped output
);

genvar idx;
logic  ce_of_tap_sfr [LATENCY];
logic  ce_tap        [LATENCY];

`GENERATE_START
for (idx = 0; idx < LATENCY; idx++) begin : ce_tap_sfr
    assign ce_of_tap_sfr[idx] = 1'b1;
end : ce_tap_sfr
`GENERATE_END

hs_dpath_sfr_ce_tap #(
    .RESET_VALUE(1'b0   ),
    .LATENCY    (LATENCY),
    .DATA_TYPE  (logic  )
)
ce_chain_sfr_inst (
    .clk    (clk          ),
    .aresetn(aresetn      ),
    .ce     (ce_of_tap_sfr),
    .din    (ce           ),
    .dout   (ce_tap       )
);

`GENERATE_START
for (idx = 0; idx <= LATENCY; idx++) begin : ce_tap_out
    assign ce_out[idx] = (idx == 0) ? ce : ce_tap[idx - 1];
end : ce_tap_out
`GENERATE_END

endmodule : hs_dpath_ce_chain
