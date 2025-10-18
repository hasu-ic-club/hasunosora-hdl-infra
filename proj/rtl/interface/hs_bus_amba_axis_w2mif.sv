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
// FILE NAME: hs_bus_amba_axis_w2mif.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a0
// VERSION DESCRIPTION: First Edition
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/10/2     First Edition
//-------------------------------------------------------------------------
// PURPOSE: Wire to standard ARM AMBA AXI-Stream interface master adapter
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// TDATA_WIDTH         1~16777216  Data width                  8
// TID_WIDTH           0~128       ID width                    1
// TDEST_WIDTH         0~128       Destination width           1
// TUSER_WIDTH         0~16777216  User field width            1
//-FHDR--------------------------------------------------------------------

// Wire to standard ARM AMBA AXI-Stream interface master adapter
module hs_bus_amba_axis_w2mif
#(
    parameter int TDATA_WIDTH = 8,
    parameter int TID_WIDTH   = 1,
    parameter int TDEST_WIDTH = 1,
    parameter int TUSER_WIDTH = 1,
    parameter int TSTRB_WIDTH = TDATA_WIDTH / 8,
    parameter int TKEEP_WIDTH = TDATA_WIDTH / 8
)
(
    // Wire
    input                        logic                   s_axis_tvalid,
    output                       logic                   s_axis_tready,
    input                        logic [TDATA_WIDTH-1:0] s_axis_tdata,
    input                        logic [TSTRB_WIDTH-1:0] s_axis_tstrb,
    input                        logic [TKEEP_WIDTH-1:0] s_axis_tkeep,
    input                        logic                   s_axis_tlast,
    input                        logic [TID_WIDTH-1:0]   s_axis_tid,
    input                        logic [TDEST_WIDTH-1:0] s_axis_tdest,
    input                        logic [TUSER_WIDTH-1:0] s_axis_tuser,
    input                        logic                   s_axis_twakeup,

    // Interface
    hs_bus_amba_axis_if.master                         m_axis_if
);

always_comb begin : axis_forward
    m_axis_if.tvalid  = s_axis_tvalid;
    s_axis_tready     = m_axis_if.tready;
    m_axis_if.tdata   = s_axis_tdata;
    m_axis_if.tstrb   = s_axis_tstrb;
    m_axis_if.tkeep   = s_axis_tkeep;
    m_axis_if.tlast   = s_axis_tlast;
    m_axis_if.tid     = s_axis_tid;
    m_axis_if.tdest   = s_axis_tdest;
    m_axis_if.tuser   = s_axis_tuser;
    m_axis_if.twakeup = s_axis_twakeup;
end : axis_forward

endmodule : hs_bus_amba_axis_w2mif