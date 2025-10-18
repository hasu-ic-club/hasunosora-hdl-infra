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
// FILE NAME: hs_bus_amba_axi_if.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a0
// VERSION DESCRIPTION: First Edition
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/10/16    First Edition
//-------------------------------------------------------------------------
// PURPOSE: Standard ARM AMBA AXI5-Full interface
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

// Standard ARM AMBA AXI5-Full interface
interface hs_bus_amba_axi_if
    import hs_bus_amba_axi_typedefs_pkg::*;
    #(
        parameter int ID_W_WIDTH       = 1,
        parameter int ID_R_WIDTH       = 1,
        parameter int ADDR_WIDTH       = 32,
        parameter int DATA_WIDTH       = 32,
        parameter int USER_REQ_WIDTH   = 1,
        parameter int USER_DATA_WIDTH  = 1,
        parameter int USER_RESP_WIDTH  = 1,
        parameter int SUBSYSID_WIDTH   = 3,
        parameter int BRESP_WIDTH      = 2,
        parameter int RRESP_WIDTH      = 2,
        parameter int NUM_RP_AWW       = 1,
        parameter int NUM_RP_AR        = 1,
        parameter int PAS_WIDTH        = 1,
        parameter int AWSNOOP_WIDTH    = 1,
        parameter int LOOP_W_WIDTH     = 1,
        parameter int LOOP_R_WIDTH     = 1,
        parameter int SECSID_WIDTH     = 1,
        parameter int SID_WIDTH        = 1,
        parameter int SSID_WIDTH       = 1,
        parameter int MECID_WIDTH      = 1,
        parameter int MPAM_WIDTH       = 1,
        parameter int AWCMO_WIDTH      = 1,
        parameter int ACT_W_WIDTH      = 1,
        parameter int ACT_R_WIDTH      = 1,
        parameter int RCHUNKNUM_WIDTH  = 1,
        parameter int RCHUNKSTRB_WIDTH = 1
    )
    (
        input logic aclk,
        input logic aresetn
    );

    localparam int                 STRB_WIDTH       = DATA_WIDTH / 8;
    localparam int                 POISON_WIDTH     = int'($ceil(DATA_WIDTH / 8.0));
    localparam int                 AWRP_WIDTH       = $clog2(NUM_RP_AWW);
    localparam int                 RRP_WIDTH        = $clog2(NUM_RP_AR);
    localparam int                 TAG_WIDTH        = int'($ceil(DATA_WIDTH / 128.0)) * 4;
    localparam int                 TAG_UPDATE_WIDTH = int'($ceil(DATA_WIDTH / 128.0));

    // Write request channel
    logic                          awvalid;
    logic                          awready;
    logic                          awpending;                                             // Indicate that a transfer might occur in the following cycle
    logic [NUM_RP_AWW - 1:0]       awcrdt;                                                // Asserted HIGH to give one AW credit on the respective RP
    logic                          awcrdtsh;                                              // Asserted HIGH to give one shared AW credit
    logic [AWRP_WIDTH - 1:0]       awrp;                                                  // Encoded indicator of the Resource Plane number for an AW transfer
    logic                          awsharedcrd;                                           // Asserted HIGH to indicate that an AW transfer is using a shared credit
    logic [ID_W_WIDTH - 1:0]       awid;                                                  // Transaction identifier used for the ordering
    logic [ADDR_WIDTH - 1:0]       awaddr;
    logic [3:0]                    awregion;                                              // Identify different address regions
    logic [7:0]                    awlen;                                                 // The total number of transfers in a transaction (-1)
    logic [2:0]                    awsize;                                                // Indicates the maximum number of bytes in each data transfer within a transaction
    axburst_e                      awburst;
    logic                          awlock;                                                // Asserted high to indicate that an exclusive access is required
    awcache_s                      awcache;
    axprot_s                       awprot;                                                // Protection attributes for a request
    logic                          awnse;                                                 // Extends AWPROT[1] to include Root and Realm address spaces
    logic [PAS_WIDTH - 1:0]        awpas;                                                 // Physical address space (PAS) of a transaction
    logic                          awinst;                                                // LOW to indicate this is a data access, HIGH for an instruction access (=AWPROT[2])
    logic                          awpriv;                                                // LOW to indicate this is an unprivileged access, HIGH for a privileged access (=AWPROT[0])
    logic [3:0]                    awqos;                                                 // Quality of Service identifier used to distinguish between different traffic streams
    logic [USER_REQ_WIDTH - 1:0]   awuser;
    axdomain_e                     awdomain;                                              // Shareability domain of a request
    logic [AWSNOOP_WIDTH - 1:0]    awsnoop;                                               // Opcode for requests using the write channels
    logic [10:0]                   awstashnid;                                            // Node Identifier of the target for a stash operation
    logic                          awstashniden;                                          // HIGH to indicate that the AWSTASHNID signal is valid
    logic [4:0]                    awstashlpid;                                           // Logical Processor Identifier within the target for a stash operation
    logic                          awstashlpiden;                                         // HIGH to indicate that the AWSTASHLPID signal is valid
    logic                          awtrace;
    logic [LOOP_W_WIDTH - 1:0]     awloop;                                                // Loopback signal
    logic                          awmmuvalid;                                            // MMU qualifier signal
    logic [SECSID_WIDTH - 1:0]     awmmusecsid;                                           // Secure Stream Identifier for untranslated transactions
    logic [SID_WIDTH - 1:0]        awmmusid;                                              // Stream Identifier for untranslated transactions
    logic                          awmmussidv;                                            // Asserted HIGH to indicate that a transaction has a valid substream identifier
    logic [SSID_WIDTH - 1:0]       awmmussid;                                             // Substream identifier for untranslated transactions
    logic                          awmmuatst;                                             // Indicates that the transaction has already undergone PCIe ATS translation
    axmmuflow_e                    awmmuflow;                                             // Indicates the SMMU flow for managing translation faults for this transaction
    logic                          awmmupasunknown;                                       // HIGH to indicate that there is no PAS
    logic                          awmmupm;                                               // Protected Mode indicator
    logic [3:0]                    awpbha;                                                // Page-based hardware attributes (PBHA)
    logic [MECID_WIDTH - 1:0]      awmecid;                                               // RME Memory Encryption Context (MEC) identifier
    logic [3:0]                    awnsaid;                                               // Non-secure access identifier
    logic [SUBSYSID_WIDTH - 1:0]   awsubsysid;                                            // Subsystem identifier
    awatop_s                       awatop;                                                // Type and endianness of atomic transaction
    logic [MPAM_WIDTH - 1:0]       awmpam;                                                // Memory System Resource Partitioning and Monitoring (MPAM) information
    logic                          awidunq;                                               // If asserted high, the ID for this transfer is unique-in-flight
    logic [AWCMO_WIDTH - 1:0]      awcmo;                                                 // Type of CMO that is requested
    awtagop_e                      awtagop;                                               // Indicates if MTE tags are requested with a read transaction.
    logic [ACT_W_WIDTH - 1:0]      awact;                                                 // ACT payload on the request channel
    logic                          awactv;                                                // Asserted HIGH to indicate that this is an ACT request and AWACT contains a valid payload

    // Write data channel
    logic                          wvalid;
    logic                          wready;
    logic                          wpending;                                              // Indicates that a transfer might occur in the following cycle
    logic [NUM_RP_AWW - 1:0]       wcrdt;                                                 // Asserted HIGH to give one W credit on the respective RP
    logic                          wcrdtsh;                                               // Asserted HIGH to give one shared W credit, supports up to one shared credit per cycle
    logic [AWRP_WIDTH - 1:0]       wrp;                                                   // Encoded indicator of the Resource Plane number for a W transfer
    logic                          wsharedcrd;                                            // Asserted HIGH to indicate that a W transfer is using a shared credit
    logic [DATA_WIDTH - 1:0]       wdata;
    logic [STRB_WIDTH - 1:0]       wstrb;
    logic [TAG_WIDTH - 1:0]        wtag;                                                  // Memory tag associated with data
    logic [TAG_UPDATE_WIDTH - 1:0] wtagupdate;                                            // Indicates which tags must be written to memory when AWTAGOP is Update
    logic                          wlast;                                                 // Indicates the last read data transfer of a transaction
    logic [USER_DATA_WIDTH - 1:0]  wuser;
    logic [POISON_WIDTH - 1:0]     wpoison;                                               // Asserted high to indicate that the data in this transfer is corrupted
    logic                          wtrace;

    // Write response channel
    logic                          bvalid;
    logic                          bready;
    logic                          bpending;                                              // Indicates that a transfer might occur in the following cycle
    logic                          bcrdt;                                                 // Asserted HIGH to give one B credit
    logic [ID_W_WIDTH - 1:0]       bid;                                                   // Transaction identifier used for the ordering
    logic                          bidunq;                                                // If asserted high, the ID for this transfer is unique-in-flight
    logic [BRESP_WIDTH - 1:0]      bresp;
    logic                          bcomp;
    logic                          bpersist;
    logic [2:0]                    btagmatch;
    logic [USER_RESP_WIDTH - 1:0]  buser;
    logic                          btrace;
    logic [LOOP_W_WIDTH - 1:0]     bloop;                                                 // Loopback signal
    xbusy_e                        bbusy;                                                 // Indicates the current level of Subordinate activity in a transaction response

    // Read request channel
    logic                          arvalid;
    logic                          arready;
    logic                          arpending;                                             // Indicate that a transfer mightoccur in the following cycle
    logic [NUM_RP_AR - 1:0]        arcrdt;                                                // Asserted HIGH to give one AR credit on the respective RP
    logic                          arcrdtsh;                                              // Asserted HIGH to give one shared AR credit
    logic [RRP_WIDTH - 1:0]        arrp;                                                  // Encoded indicator of the Resource Plane number for an AR transfer
    logic                          arsharedcrd;                                           // Asserted HIGH to indicate that an AR transfer is using a shared credit
    logic [ID_R_WIDTH - 1:0]       arid;                                                  // Transaction identifier used for the ordering
    logic [ADDR_WIDTH - 1:0]       araddr;
    logic [3:0]                    arregion;                                              // Identify different address regions
    logic [7:0]                    arlen;                                                 // The total number of transfers in a transaction (-1)
    logic [2:0]                    arsize;                                                // Indicates the maximum number of bytes in each data transfer within a transaction
    axburst_e                      arburst;
    logic                          arlock;                                                // Asserted high to indicate that an exclusive access is required
    arcache_s                      arcache;
    axprot_s                       arprot;                                                // Protection attributes for a request
    logic                          arnse;                                                 // Extends ARPROT[1] to include Root and Realm address spaces
    logic [PAS_WIDTH - 1:0]        arpas;                                                 // Physical address space (PAS) of a transaction
    logic                          arinst;                                                // LOW to indicate this is a data access, HIGH for an instruction access (=ARPROT[2])
    logic                          arpriv;                                                // LOW to indicate this is an unprivileged access, HIGH for a privileged access (=ARPROT[0])
    logic [3:0]                    arqos;                                                 // Quality of Service identifier used to distinguish between different traffic streams
    logic [USER_REQ_WIDTH - 1:0]   aruser;
    axdomain_e                     ardomain;                                              // Shareability domain of a request
    logic [AWSNOOP_WIDTH - 1:0]    arsnoop;                                               // Opcode for requests using the read channels
    logic                          artrace;
    logic [LOOP_R_WIDTH - 1:0]     arloop;                                                // Loopback signal
    logic                          armmuvalid;                                            // MMU qualifier signal
    logic [SECSID_WIDTH - 1:0]     armmusecsid;                                           // Secure Stream Identifier for untranslated transactions
    logic [SID_WIDTH - 1:0]        armmusid;                                              // Stream Identifier for untranslated transactions
    logic                          armmussidv;                                            // Asserted HIGH to indicate that a transaction has a valid substream identifier
    logic [SSID_WIDTH - 1:0]       armmussid;                                             // Substream identifier for untranslated transactions
    logic                          armmuatst;                                             // Indicates the SMMU flow for managing translation faults for this transaction
    axmmuflow_e                    armmuflow;                                             // Indicates that the transaction has already undergone PCIe ATS translation
    logic                          armmupasunknown;                                       // HIGH to indicate that there is no PAS
    logic                          armmupm;                                               // Protected Mode indicator
    logic [3:0]                    arpbha;                                                // Page-based hardware attributes (PBHA)
    logic [MECID_WIDTH - 1:0]      armecid;                                               // RME Memory Encryption Context (MEC) identifier
    logic [3:0]                    arnsaid;                                               // Non-secure access identifier
    logic [SUBSYSID_WIDTH - 1:0]   arsubsysid;                                            // Subsystem identifier
    logic [MPAM_WIDTH - 1:0]       armpam;                                                // Memory System Resource Partitioning and Monitoring (MPAM) information
    logic                          archunken;                                             // Indicate the subordinate can send read data in 128b chunks
    logic                          aridunq;                                               // If asserted high, the ID for this transfer is unique-in-flight
    artagop_e                      artagop;                                               // Indicates if MTE tags are requested with a read transaction.
    logic [ACT_R_WIDTH - 1:0]      aract;                                                 // ACT payload on the request channel
    logic                          aractv;                                                // Asserted HIGH to indicate that this is an ACT request and ARACT contains a valid payload

    // Read data channel
    logic                          rvalid;
    logic                          rready;
    logic                          rpending;                                              // Indicates that a transfer might occur in the following cycle
    logic                          rcrdt;                                                 // Asserted HIGH to give one R credit on the respective RP
    logic [ID_R_WIDTH - 1:0]       rid;                                                   // Transaction identifier used for the ordering
    logic                          ridunq;                                                // If asserted high, the ID for this transfer is unique-in-flight
    logic [DATA_WIDTH - 1:0]       rdata;
    logic [TAG_WIDTH - 1:0]        rtag;                                                  // Memory tag associated with data
    logic [RRESP_WIDTH - 1:0]      rresp;
    logic                          rlast;                                                 // Indicates the last read data transfer of a transaction
    logic [USER_RESP_WIDTH - 1:0]  ruser;
    logic [POISON_WIDTH - 1:0]     rpoison;                                               // Asserted high to indicate that the data in this transfer is corrupted
    logic                          rtrace;
    logic [LOOP_R_WIDTH - 1:0]     rloop;                                                 // Loopback signal
    logic                          rchunkv;                                               // Asserted high to indicate that RCHUNKNUM and RCHUNKSTRB are valid
    logic [RCHUNKNUM_WIDTH - 1:0]  rchunknum;                                             // Indicates the chunk number being transferred
    logic [RCHUNKSTRB_WIDTH - 1:0] rchunkstrb;                                            // Indicates the read data chunks that are valid for this transfer
    xbusy_e                        rbusy;                                                 // Indicates the current level of Subordinate activity in a transaction response

    // Master
    modport master
    (
        // Write address channel
        output awvalid, awpending, awrp, awsharedcrd, awid, awaddr, awregion,
               awlen, awsize, awburst, awlock, awcache, awprot, awnse, awpas, awinst,
               awpriv, awqos, awuser, awdomain, awsnoop,
               awstashnid, awstashniden, awstashlpid, awstashlpiden, awtrace, awloop,
               awmmuvalid, awmmusecsid, awmmusid, awmmussidv, awmmussid, awmmuatst,
               awmmuflow, awmmupasunknown, awmmupm, awpbha, awmecid, awnsaid,
               awsubsysid, awatop, awmpam, awidunq, awcmo, awtagop, awact, awactv,

        input  awready, awcrdt, awcrdtsh,

        // Write data channel
        output wvalid, wpending, wrp, wsharedcrd, wdata, wstrb, wtag, wtagupdate,
               wlast, wuser, wpoison, wtrace,
        input  wready, wcrdt, wcrdtsh,

        // Write response channel
        input  bvalid, bpending, bid, bidunq, bresp, bcomp, bpersist, btagmatch,
               buser, btrace, bloop, bbusy,
        output bready, bcrdt,

        // Read address channel
        output arvalid, arpending, arrp, arsharedcrd, arid, araddr, arregion,
               arlen, arsize, arburst, arlock, arcache, arprot, arnse, arpas, arinst,
               arpriv, arqos, aruser, ardomain, arsnoop, artrace, arloop,
               armmuvalid, armmusecsid, armmusid, armmussidv, armmussid, armmuatst,
               armmuflow, armmupasunknown, armmupm, arpbha, armecid, arnsaid,
               arsubsysid, armpam, archunken, aridunq, artagop, aract, aractv,
        input  arready, arcrdt, arcrdtsh,

        // Read data channel
        input  rvalid, rpending, rid, ridunq, rdata, rtag, rresp, rlast, ruser,
               rpoison, rtrace, rloop, rchunkv, rchunknum, rchunkstrb, rbusy,
        output rready, rcrdt
    );

    // Slave
    modport slave
    (
        // Write address channel
        input  awvalid, awpending, awrp, awsharedcrd, awid, awaddr, awregion,
               awlen, awsize, awburst, awlock, awcache, awprot, awnse, awpas, awinst,
               awpriv, awqos, awuser, awdomain, awsnoop,
               awstashnid, awstashniden, awstashlpid, awstashlpiden, awtrace, awloop,
               awmmuvalid, awmmusecsid, awmmusid, awmmussidv, awmmussid, awmmuatst,
               awmmuflow, awmmupasunknown, awmmupm, awpbha, awmecid, awnsaid,
               awsubsysid, awatop, awmpam, awidunq, awcmo, awtagop, awact, awactv,

        output awready, awcrdt, awcrdtsh,

        // Write data channel
        input  wvalid, wpending, wrp, wsharedcrd, wdata, wstrb, wtag, wtagupdate,
               wlast, wuser, wpoison, wtrace,
        output wready, wcrdt, wcrdtsh,

        // Write response channel
        output bvalid, bpending, bid, bidunq, bresp, bcomp, bpersist, btagmatch,
               buser, btrace, bloop, bbusy,
        input  bready, bcrdt,

        // Read address channel
        input  arvalid, arpending, arrp, arsharedcrd, arid, araddr, arregion,
               arlen, arsize, arburst, arlock, arcache, arprot, arnse, arpas, arinst,
               arpriv, arqos, aruser, ardomain, arsnoop, artrace, arloop,
               armmuvalid, armmusecsid, armmusid, armmussidv, armmussid, armmuatst,
               armmuflow, armmupasunknown, armmupm, arpbha, armecid, arnsaid,
               arsubsysid, armpam, archunken, aridunq, artagop, aract, aractv,
        output arready, arcrdt, arcrdtsh,

        // Read data channel
        output rvalid, rpending, rid, ridunq, rdata, rtag, rresp, rlast, ruser,
               rpoison, rtrace, rloop, rchunkv, rchunknum, rchunkstrb, rbusy,
        input  rready, rcrdt
    );

    // Basic assert for interface signals
    //  1. AW handshake stable
    property p_aw_hold_payload_until_handshake;
        @(posedge aclk) disable iff (!aresetn)
            awvalid && !awready |-> ##1 (
                $stable(awpending) &&
                $stable(awrp) &&
                $stable(awsharedcrd) &&
                $stable(awid) &&
                $stable(awaddr) &&
                $stable(awregion) &&
                $stable(awlen) &&
                $stable(awsize) &&
                $stable(awburst) &&
                $stable(awlock) &&
                $stable(awcache) &&
                $stable(awprot) &&
                $stable(awnse) &&
                $stable(awpas) &&
                $stable(awinst) &&
                $stable(awpriv) &&
                $stable(awqos) &&
                $stable(awuser) &&
                $stable(awdomain) &&
                $stable(awsnoop) &&
                $stable(awstashnid) &&
                $stable(awstashniden) &&
                $stable(awstashlpid) &&
                $stable(awstashlpiden) &&
                $stable(awtrace) &&
                $stable(awloop) &&
                $stable(awmmuvalid) &&
                $stable(awmmusecsid) &&
                $stable(awmmusid) &&
                $stable(awmmussidv) &&
                $stable(awmmussid) &&
                $stable(awmmuatst) &&
                $stable(awmmuflow) &&
                $stable(awmmupasunknown) &&
                $stable(awmmupm) &&
                $stable(awpbha) &&
                $stable(awmecid) &&
                $stable(awnsaid) &&
                $stable(awsubsysid) &&
                $stable(awatop) &&
                $stable(awmpam) &&
                $stable(awidunq) &&
                $stable(awcmo) &&
                $stable(awtagop) &&
                $stable(awact) &&
                $stable(awactv)
            );
    endproperty : p_aw_hold_payload_until_handshake
    assert property (p_aw_hold_payload_until_handshake)
    else $error("AXI-Lite AW payload changed before handshake");

    //  2. W handshake stable
    property p_w_hold_payload_until_handshake;
        @(posedge aclk) disable iff (!aresetn)
            wvalid && !wready |-> ##1 (
                $stable(wvalid) &&
                $stable(wpending) &&
                $stable(wrp) &&
                $stable(wsharedcrd) &&
                $stable(wdata) &&
                $stable(wstrb) &&
                $stable(wtag) &&
                $stable(wtagupdate) &&
                $stable(wlast) &&
                $stable(wuser) &&
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
                $stable(bvalid) &&
                $stable(bpending) &&
                $stable(bid) &&
                $stable(bidunq) &&
                $stable(bresp) &&
                $stable(bcomp) &&
                $stable(bpersist) &&
                $stable(btagmatch) &&
                $stable(buser) &&
                $stable(btrace) &&
                $stable(bloop) &&
                $stable(bbusy)
            );
    endproperty : p_b_hold_payload_until_handshake
    assert property (p_b_hold_payload_until_handshake)
    else $error("AXI-Lite B payload changed before handshake");

    //  4. AR handshake stable
    property p_ar_hold_payload_until_handshake;
        @(posedge aclk) disable iff (!aresetn)
            arvalid && !arready |-> ##1 (
                $stable(arvalid) &&
                $stable(arpending) &&
                $stable(arrp) &&
                $stable(arsharedcrd) &&
                $stable(arid) &&
                $stable(araddr) &&
                $stable(arregion) &&
                $stable(arlen) &&
                $stable(arsize) &&
                $stable(arburst) &&
                $stable(arlock) &&
                $stable(arcache) &&
                $stable(arprot) &&
                $stable(arnse) &&
                $stable(arpas) &&
                $stable(arinst) &&
                $stable(arpriv) &&
                $stable(arqos) &&
                $stable(aruser) &&
                $stable(ardomain) &&
                $stable(arsnoop) &&
                $stable(artrace) &&
                $stable(arloop) &&
                $stable(armmuvalid) &&
                $stable(armmusecsid) &&
                $stable(armmusid) &&
                $stable(armmussidv) &&
                $stable(armmussid) &&
                $stable(armmuatst) &&
                $stable(armmuflow) &&
                $stable(armmupasunknown) &&
                $stable(armmupm) &&
                $stable(arpbha) &&
                $stable(armecid) &&
                $stable(arnsaid) &&
                $stable(arsubsysid) &&
                $stable(armpam) &&
                $stable(archunken) &&
                $stable(aridunq) &&
                $stable(artagop) &&
                $stable(aract) &&
                $stable(aractv)
            );
    endproperty : p_ar_hold_payload_until_handshake
    assert property (p_ar_hold_payload_until_handshake)
    else $error("AXI-Lite AR payload changed before handshake");

    //  5. R handshake stable
    property p_r_hold_payload_until_handshake;
        @(posedge aclk) disable iff (!aresetn)
            rvalid && !rready |-> ##1 (
                $stable(rvalid) &&
                $stable(rpending) &&
                $stable(rid) &&
                $stable(ridunq) &&
                $stable(rdata) &&
                $stable(rtag) &&
                $stable(rresp) &&
                $stable(rlast) &&
                $stable(ruser) &&
                $stable(rpoison) &&
                $stable(rtrace) &&
                $stable(rloop) &&
                $stable(rchunkv) &&
                $stable(rchunknum) &&
                $stable(rchunkstrb) &&
                $stable(rbusy)
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
endinterface : hs_bus_amba_axi_if
