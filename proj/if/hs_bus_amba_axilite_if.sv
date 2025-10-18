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
// FILE NAME: hs_bus_amba_axilite_if.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a2
// VERSION DESCRIPTION: New version with pre-define enumeration/structures
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/10/2     First Edition
// 0.1a1      O. Tsusaki    2025/10/15    Add basic assertions and coverages
// 0.1a2      O. Tsusaki    2025/10/16    Import hs_ifr_amba_axi_typedefs_pkg
//                                        to use pre-defined enumeration and structures
//                                        to simplify the interface definition
//-------------------------------------------------------------------------
// PURPOSE: Standard ARM AMBA AXI5-Lite interface
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

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// Standard ARM AMBA AXI5-Lite interface
interface hs_bus_amba_axilite_if
    import hs_bus_amba_axi_typedefs_pkg::*;
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
        input logic aclk,
        input logic aresetn
    );

    // Write request channel
    logic                         awready;
    logic                         awvalid;
    logic [ID_W_WIDTH - 1:0]      awid;
    logic [ADDR_WIDTH - 1:0]      awaddr;
    logic [2:0]                   awsize;
    axprot_s                      awprot;
    logic                         awtrace;
    logic [SUBSYSID_WIDTH - 1:0]  awsubsysid;
    logic                         awidunq;

    // Write data channel
    logic                         wvalid;
    logic                         wready;
    logic [DATA_WIDTH - 1:0]      wdata;
    logic [STRB_WIDTH - 1:0]      wstrb;
    logic [USER_DATA_WIDTH - 1:0] wuser;
    logic [POISON_WIDTH - 1:0]    wpoison;
    logic                         wtrace;

    // Write response channel
    logic                         bvalid;
    logic                         bready;
    logic [ID_W_WIDTH - 1:0]      bid;
    logic                         bidunq;
    logic [BRESP_WIDTH - 1:0]     bresp;
    logic [USER_RESP_WIDTH - 1:0] buser;
    logic                         btrace;

    // Read request channel
    logic                         arvalid;
    logic                         arready;
    logic [ID_R_WIDTH - 1:0]      arid;
    logic [ADDR_WIDTH - 1:0]      araddr;
    logic [2:0]                   arsize;
    axprot_s                      arprot;
    logic [USER_DATA_WIDTH - 1:0] aruser;
    logic [POISON_WIDTH - 1:0]    artrace;
    logic [SUBSYSID_WIDTH - 1:0]  arsubsysid;
    logic                         aridunq;

    // Read data channel
    logic                         rvalid;
    logic                         rready;
    logic [ID_R_WIDTH - 1:0]      rid;
    logic                         ridunq;
    logic [DATA_WIDTH - 1:0]      rdata;
    logic [RRESP_WIDTH - 1:0]     rresp;
    logic [USER_RESP_WIDTH - 1:0] ruser;
    logic [POISON_WIDTH - 1:0]    rpoison;
    logic                         rtrace;

    // Master
    modport master
    (
        // Write address channel
        output awvalid, awid, awaddr, awsize, awprot, awtrace, awsubsysid, awidunq,
        input  awready,

        // Write data channel
        output wvalid, wdata, wstrb, wuser, wpoison, wtrace,
        input  wready,

        // Write response channel
        input  bvalid, bid, bidunq, bresp, buser, btrace,
        output bready,

        // Read address channel
        output arvalid, arid, araddr, arsize, arprot, aruser, artrace, arsubsysid, aridunq,
        input  arready,

        // Read data channel
        input  rvalid, rid, ridunq, rdata, rresp, ruser, rpoison, rtrace,
        output rready
    );

    // Slave
    modport slave
    (
        // Write address channel
        input  awvalid, awid, awaddr, awsize, awprot, awtrace, awsubsysid, awidunq,
        output awready,

        // Write data channel
        input  wvalid, wdata, wstrb, wuser, wpoison, wtrace,
        output wready,

        // Write response channel
        output bvalid, bid, bidunq, bresp, buser, btrace,
        input  bready,

        // Read address channel
        input  arvalid, arid, araddr, arsize, arprot, aruser, artrace, arsubsysid, aridunq,
        output arready,

        // Read data channel
        output rvalid, rid, ridunq, rdata, rresp, ruser, rpoison, rtrace,
        input  rready
    );

    // Basic assert for interface signals
    //  1. AW handshake stable
    property p_aw_hold_payload_until_handshake;
        @(posedge aclk) disable iff (!aresetn)
            awvalid && !awready |-> ##1 (
                $stable(awid)      &&
                $stable(awaddr)    &&
                $stable(awsize)    &&
                $stable(awprot)    &&
                $stable(awtrace)   &&
                $stable(awsubsysid)&&
                $stable(awidunq)
            );
    endproperty : p_aw_hold_payload_until_handshake
    assert property (p_aw_hold_payload_until_handshake)
    else $error("AXI-Lite AW payload changed before handshake");

    //  2. W handshake stable
    property p_w_hold_payload_until_handshake;
        @(posedge aclk) disable iff (!aresetn)
            wvalid && !wready |-> ##1 (
                $stable(wdata)   &&
                $stable(wstrb)   &&
                $stable(wuser)   &&
                $stable(wpoison) &&
                $stable(wtrace)
            );
    endproperty : p_w_hold_payload_until_handshake
    assert property (p_w_hold_payload_until_handshake)
    else $error("AXI-Lite W payload changed before handshake");

    //  3. B handshake stable
    property p_b_hold_payload_until_handshake;
        @(posedge aclk) disable iff (!aresetn)
            bvalid && !bready |-> ##1 (
                $stable(bid)    &&
                $stable(bidunq) &&
                $stable(bresp)  &&
                $stable(buser)  &&
                $stable(btrace)
            );
    endproperty : p_b_hold_payload_until_handshake
    assert property (p_b_hold_payload_until_handshake)
    else $error("AXI-Lite B payload changed before handshake");

    //  4. AR handshake stable
    property p_ar_hold_payload_until_handshake;
        @(posedge aclk) disable iff (!aresetn)
            arvalid && !arready |-> ##1 (
                $stable(arid)      &&
                $stable(araddr)    &&
                $stable(arsize)    &&
                $stable(arprot)    &&
                $stable(aruser)    &&
                $stable(artrace)   &&
                $stable(arsubsysid)&&
                $stable(aridunq)
            );
    endproperty : p_ar_hold_payload_until_handshake
    assert property (p_ar_hold_payload_until_handshake)
    else $error("AXI-Lite AR payload changed before handshake");

    //  5. R handshake stable
    property p_r_hold_payload_until_handshake;
        @(posedge aclk) disable iff (!aresetn)
            rvalid && !rready |-> ##1 (
                $stable(rid)    &&
                $stable(ridunq) &&
                $stable(rdata)  &&
                $stable(rresp)  &&
                $stable(ruser)  &&
                $stable(rpoison)&&
                $stable(rtrace)
            );
    endproperty : p_r_hold_payload_until_handshake
    assert property (p_r_hold_payload_until_handshake)
    else $error("AXI-Lite R payload changed before handshake");

    // 6. After AWVALID = 1, AWVALID should not be deasserted until AWREADY = 1
    property p_awvalid_hold_until_awready;
        @(posedge aclk) disable iff (!aresetn)
            awvalid && !awready |=> awvalid;
    endproperty : p_awvalid_hold_until_awready
    assert property (p_awvalid_hold_until_awready)
    else $error("AXI-Lite AWVALID deasserted before AWREADY handshake");

    // 7. After WVALID = 1, WVALID should not be deasserted until WREADY = 1
    property p_wvalid_hold_until_wready;
        @(posedge aclk) disable iff (!aresetn)
            wvalid && !wready |=> wvalid;
    endproperty : p_wvalid_hold_until_wready
    assert property (p_wvalid_hold_until_wready)
    else $error("AXI-Lite WVALID deasserted before WREADY handshake");

    // 8. After BVALID = 1, BVALID should not be deasserted until BREADY = 1
    property p_bvalid_hold_until_bready;
        @(posedge aclk) disable iff (!aresetn)
            bvalid && !bready |=> bvalid;
    endproperty : p_bvalid_hold_until_bready
    assert property (p_bvalid_hold_until_bready)
    else $error("AXI-Lite BVALID deasserted before BREADY handshake");

    // 9. After ARVALID = 1, ARVALID should not be deasserted until ARREADY = 1
    property p_arvalid_hold_until_arready;
        @(posedge aclk) disable iff (!aresetn)
            arvalid && !arready |=> arvalid;
    endproperty : p_arvalid_hold_until_arready
    assert property (p_arvalid_hold_until_arready)
    else $error("AXI-Lite ARVALID deasserted before ARREADY handshake");

    // 10. After RVALID = 1, RVALID should not be deasserted until RREADY = 1
    property p_rvalid_hold_until_rready;
        @(posedge aclk) disable iff (!aresetn)
            rvalid && !rready |=> rvalid;
    endproperty : p_rvalid_hold_until_rready
    assert property (p_rvalid_hold_until_rready)
    else $error("AXI-Lite RVALID deasserted before RREADY handshake");

    // 11. Coverage point for AW handshake
    cover property ( @(posedge aclk) disable iff (!aresetn)  awvalid && awready);

    // 12. Coverage point for W handshake
    cover property ( @(posedge aclk) disable iff (!aresetn)  wvalid && wready);

    // 13. Coverage point for B handshake
    cover property ( @(posedge aclk) disable iff (!aresetn)  bvalid && bready);

    // 14. Coverage point for AR handshake
    cover property ( @(posedge aclk) disable iff (!aresetn)  arvalid && arready);

    // 15. Coverage point for R handshake
    cover property ( @(posedge aclk) disable iff (!aresetn)  rvalid && rready);
endinterface : hs_bus_amba_axilite_if


