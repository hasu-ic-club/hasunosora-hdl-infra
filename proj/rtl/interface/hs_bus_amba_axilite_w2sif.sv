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
// FILE NAME: hs_bus_amba_axilite_w2sif.sv
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
// PURPOSE: Wire to standard ARM AMBA AXI5-Lite interface slave adapter
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

// Wire to standard ARM AMBA AXI5-Lite interface slave adapter
module hs_bus_amba_axilite_w2sif
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
    output                         logic                          m_axilite_awvalid,
    input                          logic                          m_axilite_awready,
    output                         logic [ID_W_WIDTH - 1:0]       m_axilite_awid,
    output                         logic [ADDR_WIDTH - 1:0]       m_axilite_awaddr,
    output                         logic [2:0]                    m_axilite_awsize,
    output                         logic [2:0]                    m_axilite_awprot,
    output                         logic                          m_axilite_awtrace,
    output                         logic [SUBSYSID_WIDTH - 1:0]   m_axilite_awsubsysid,
    output                         logic                          m_axilite_awidunq,

    // Write data channel
    output                         logic                          m_axilite_wvalid,
    input                          logic                          m_axilite_wready,
    output                         logic [DATA_WIDTH - 1:0]       m_axilite_wdata,
    output                         logic [STRB_WIDTH - 1:0]       m_axilite_wstrb,
    output                         logic [USER_DATA_WIDTH - 1:0]  m_axilite_wuser,
    output                         logic [POISON_WIDTH - 1:0]     m_axilite_wpoison,
    output                         logic                          m_axilite_wtrace,

    // Write response channel
    input                          logic                          m_axilite_bvalid,
    output                         logic                          m_axilite_bready,
    input                          logic [ID_W_WIDTH - 1:0]       m_axilite_bid,
    input                          logic                          m_axilite_bidunq,
    input                          logic [BRESP_WIDTH - 1:0]      m_axilite_bresp,
    input                          logic [USER_RESP_WIDTH - 1:0]  m_axilite_buser,
    input                          logic                          m_axilite_btrace,

    // Read request channel
    output                         logic                          m_axilite_arvalid,
    input                          logic                          m_axilite_arready,
    output                         logic [ID_R_WIDTH - 1:0]       m_axilite_arid,
    output                         logic [ADDR_WIDTH - 1:0]       m_axilite_araddr,
    output                         logic [2:0]                    m_axilite_arsize,
    output                         logic [2:0]                    m_axilite_arprot,
    output                         logic [USER_DATA_WIDTH - 1:0]  m_axilite_aruser,
    output                         logic [POISON_WIDTH - 1:0]     m_axilite_artrace,
    output                         logic [SUBSYSID_WIDTH - 1:0]   m_axilite_arsubsysid,
    output                         logic                          m_axilite_aridunq,

    // Read data channel
    input                          logic                          m_axilite_rvalid,
    output                         logic                          m_axilite_rready,
    input                          logic [ID_R_WIDTH - 1:0]       m_axilite_rid,
    input                          logic                          m_axilite_ridunq,
    input                          logic [DATA_WIDTH - 1:0]       m_axilite_rdata,
    input                          logic [RRESP_WIDTH - 1:0]      m_axilite_rresp,
    input                          logic [USER_RESP_WIDTH - 1:0]  m_axilite_ruser,
    input                          logic [POISON_WIDTH - 1:0]     m_axilite_rpoison,
    input                          logic                          m_axilite_rtrace,

    // Interface
    hs_bus_amba_axilite_if.slave                                s_axilite_if
);

always_comb begin : axilite_forward
    // Write address channel
    s_axilite_if.awready = m_axilite_awready;
    m_axilite_awvalid    = s_axilite_if.awvalid;
    m_axilite_awid       = s_axilite_if.awid;
    m_axilite_awaddr     = s_axilite_if.awaddr;
    m_axilite_awsize     = s_axilite_if.awsize;
    m_axilite_awprot     = s_axilite_if.awprot;
    m_axilite_awtrace    = s_axilite_if.awtrace;
    m_axilite_awsubsysid = s_axilite_if.awsubsysid;
    m_axilite_awidunq    = s_axilite_if.awidunq;

    // Write data channel
    m_axilite_wvalid     = s_axilite_if.wvalid;
    s_axilite_if.wready  = m_axilite_wready;
    m_axilite_wdata      = s_axilite_if.wdata;
    m_axilite_wstrb      = s_axilite_if.wstrb;
    m_axilite_wuser      = s_axilite_if.wuser;
    m_axilite_wpoison    = s_axilite_if.wpoison;
    m_axilite_wtrace     = s_axilite_if.wtrace;

    // Write response channel
    s_axilite_if.bvalid  = m_axilite_bvalid;
    m_axilite_bready     = s_axilite_if.bready;
    s_axilite_if.bid     = m_axilite_bid;
    s_axilite_if.bidunq  = m_axilite_bidunq;
    s_axilite_if.bresp   = m_axilite_bresp;
    s_axilite_if.buser   = m_axilite_buser;
    s_axilite_if.btrace  = m_axilite_btrace;

    // Read request channel
    m_axilite_arvalid    = s_axilite_if.arvalid;
    s_axilite_if.arready = m_axilite_arready;
    m_axilite_arid       = s_axilite_if.arid;
    m_axilite_araddr     = s_axilite_if.araddr;
    m_axilite_arsize     = s_axilite_if.arsize;
    m_axilite_arprot     = s_axilite_if.arprot;
    m_axilite_aruser     = s_axilite_if.aruser;
    m_axilite_artrace    = s_axilite_if.artrace;
    m_axilite_arsubsysid = s_axilite_if.arsubsysid;
    m_axilite_aridunq    = s_axilite_if.aridunq;

    // Read data channel
    s_axilite_if.rvalid  = m_axilite_rvalid;
    m_axilite_rready     = s_axilite_if.rready;
    s_axilite_if.rid     = m_axilite_rid;
    s_axilite_if.ridunq  = m_axilite_ridunq;
    s_axilite_if.rdata   = m_axilite_rdata;
    s_axilite_if.rresp   = m_axilite_rresp;
    s_axilite_if.ruser   = m_axilite_ruser;
    s_axilite_if.rpoison = m_axilite_rpoison;
    s_axilite_if.rtrace  = m_axilite_rtrace;
end : axilite_forward

endmodule : hs_bus_amba_axilite_w2sif