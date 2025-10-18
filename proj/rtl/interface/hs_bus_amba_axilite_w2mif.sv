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
// FILE NAME: hs_bus_amba_axilite_w2mif.sv
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
// PURPOSE: Wire to standard ARM AMBA AXI5-Lite interface master adapter
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// ID_W_WIDTH          1~32        Write channel width         1
// ID_R_WIDTH          1~32        Read channel width          1
// ADDR_WIDTH          1~16777216  Address width               32
// DATA_WIDTH          1~16777216  Data width                  32
// USER_DATA_WIDTH     1~16777216  User field width in data    1
// USER_RESP_WIDTH     1~16777216  User field width in resp.   1
// SUBSYSID_WIDTH      1~8         Subsystem ID width          1
// BRESP_WIDTH         0,2,3       Write response msg. width   2
// RRESP_WIDTH         0,2,3       Read response msg. width    2
//-FHDR--------------------------------------------------------------------

// Wire to standard ARM AMBA AXI5-Lite interface master adapter
module hs_bus_amba_axilite_w2mif
#(
    parameter int ID_W_WIDTH      = 1,
    parameter int ID_R_WIDTH      = 1,
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int STRB_WIDTH      = DATA_WIDTH / 8,
    parameter int USER_DATA_WIDTH = 1,
    parameter int USER_RESP_WIDTH = 1,
    parameter int POISON_WIDTH    = int'($ceil(DATA_WIDTH / 8.0)),
    parameter int SUBSYSID_WIDTH  = 3,
    parameter int BRESP_WIDTH     = 2,
    parameter int RRESP_WIDTH     = 2
)
(
    // Write request channel
    input                           logic                          s_axilite_awvalid,
    output                          logic                          s_axilite_awready,
    input                           logic [ID_W_WIDTH - 1:0]       s_axilite_awid,
    input                           logic [ADDR_WIDTH - 1:0]       s_axilite_awaddr,
    input                           logic [2:0]                    s_axilite_awsize,
    input                           logic [2:0]                    s_axilite_awprot,
    input                           logic                          s_axilite_awtrace,
    input                           logic [SUBSYSID_WIDTH - 1:0]   s_axilite_awsubsysid,
    input                           logic                          s_axilite_awidunq,

    // Write data channel
    input                           logic                          s_axilite_wvalid,
    output                          logic                          s_axilite_wready,
    input                           logic [DATA_WIDTH - 1:0]       s_axilite_wdata,
    input                           logic [STRB_WIDTH - 1:0]       s_axilite_wstrb,
    input                           logic [USER_DATA_WIDTH - 1:0]  s_axilite_wuser,
    input                           logic [POISON_WIDTH - 1:0]     s_axilite_wpoison,
    input                           logic                          s_axilite_wtrace,

    // Write response channel
    output                          logic                          s_axilite_bvalid,
    input                           logic                          s_axilite_bready,
    output                          logic [ID_W_WIDTH - 1:0]       s_axilite_bid,
    output                          logic                          s_axilite_bidunq,
    output                          logic [BRESP_WIDTH - 1:0]      s_axilite_bresp,
    output                          logic [USER_RESP_WIDTH - 1:0]  s_axilite_buser,
    output                          logic                          s_axilite_btrace,

    // Read request channel
    input                           logic                          s_axilite_arvalid,
    output                          logic                          s_axilite_arready,
    input                           logic [ID_R_WIDTH - 1:0]       s_axilite_arid,
    input                           logic [ADDR_WIDTH - 1:0]       s_axilite_araddr,
    input                           logic [2:0]                    s_axilite_arsize,
    input                           logic [2:0]                    s_axilite_arprot,
    input                           logic [USER_DATA_WIDTH - 1:0]  s_axilite_aruser,
    input                           logic [POISON_WIDTH - 1:0]     s_axilite_artrace,
    input                           logic [SUBSYSID_WIDTH - 1:0]   s_axilite_arsubsysid,
    input                           logic                          s_axilite_aridunq,

    // Read data channel
    output                          logic                          s_axilite_rvalid,
    input                           logic                          s_axilite_rready,
    output                          logic [ID_R_WIDTH - 1:0]       s_axilite_rid,
    output                          logic                          s_axilite_ridunq,
    output                          logic [DATA_WIDTH - 1:0]       s_axilite_rdata,
    output                          logic [RRESP_WIDTH - 1:0]      s_axilite_rresp,
    output                          logic [USER_RESP_WIDTH - 1:0]  s_axilite_ruser,
    output                          logic [POISON_WIDTH - 1:0]     s_axilite_rpoison,
    output                          logic                          s_axilite_rtrace,

    // Interface
    hs_bus_amba_axilite_if.master                                m_axilite_if
);

always_comb begin : axilite_forward
    // Write address channel
    s_axilite_awready        = m_axilite_if.awready;
    m_axilite_if.awvalid     = s_axilite_awvalid;
    m_axilite_if.awid        = s_axilite_awid;
    m_axilite_if.awaddr      = s_axilite_awaddr;
    m_axilite_if.awsize      = s_axilite_awsize;
    m_axilite_if.awprot      = s_axilite_awprot;
    m_axilite_if.awtrace     = s_axilite_awtrace;
    m_axilite_if.awsubsysid  = s_axilite_awsubsysid;
    m_axilite_if.awidunq     = s_axilite_awidunq;

    // Write data channel
    m_axilite_if.wvalid      = s_axilite_wvalid;
    s_axilite_wready         = m_axilite_if.wready;
    m_axilite_if.wdata       = s_axilite_wdata;
    m_axilite_if.wstrb       = s_axilite_wstrb;
    m_axilite_if.wuser       = s_axilite_wuser;
    m_axilite_if.wpoison     = s_axilite_wpoison;
    m_axilite_if.wtrace      = s_axilite_wtrace;

    // Write response channel
    s_axilite_bvalid         = m_axilite_if.bvalid;
    m_axilite_if.bready      = s_axilite_bready;
    s_axilite_bid            = m_axilite_if.bid;
    s_axilite_bidunq         = m_axilite_if.bidunq;
    s_axilite_bresp          = m_axilite_if.bresp;
    s_axilite_buser          = m_axilite_if.buser;
    s_axilite_btrace         = m_axilite_if.btrace;

    // Read request channel
    m_axilite_if.arvalid     = s_axilite_arvalid;
    s_axilite_arready        = m_axilite_if.arready;
    m_axilite_if.arid        = s_axilite_arid;
    m_axilite_if.araddr      = s_axilite_araddr;
    m_axilite_if.arsize      = s_axilite_arsize;
    m_axilite_if.arprot      = s_axilite_arprot;
    m_axilite_if.aruser      = s_axilite_aruser;
    m_axilite_if.artrace     = s_axilite_artrace;
    m_axilite_if.arsubsysid  = s_axilite_arsubsysid;
    m_axilite_if.aridunq     = s_axilite_aridunq;

    // Read data channel
    s_axilite_rvalid         = m_axilite_if.rvalid;
    m_axilite_if.rready      = s_axilite_rready;
    s_axilite_rid            = m_axilite_if.rid;
    s_axilite_ridunq         = m_axilite_if.ridunq;
    s_axilite_rdata          = m_axilite_if.rdata;
    s_axilite_rresp          = m_axilite_if.rresp;
    s_axilite_ruser          = m_axilite_if.ruser;
    s_axilite_rpoison        = m_axilite_if.rpoison;
    s_axilite_rtrace         = m_axilite_if.rtrace;
end : axilite_forward

endmodule : hs_bus_amba_axilite_w2mif