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
// FILE NAME: hs_fifo_afifo_uvm_env_pkg.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a0
// VERSION DESCRIPTION: First Edition
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/9/27     First Edition
//-------------------------------------------------------------------------
// PURPOSE: Package of enviroment definition for UVM framework of hs_fifo_afifo
//
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE


// Package of enviroment definition for UVM framework of hs_fifo_afifo
package hs_fifo_afifo_uvm_env_pkg;
    import uvm_pkg::*;
    import hs_ifr_misc_typedefs_pkg::*;
    import hs_fifo_afifo_uvm_seqitem_pkg::*;
    import hs_fifo_afifo_uvm_agent_pkg::*;
    import hs_fifo_afifo_uvm_rm_pkg::*;
    import hs_fifo_afifo_uvm_scb_pkg::*;
    import hs_fifo_afifo_uvm_seqer_pkg::*;

    `include "uvm_macros.svh"


    class fifo_verify_env extends uvm_env;
        `uvm_component_utils(fifo_verify_env)
        `uvm_new_func

        // Agents
        fifo_write_agent                          wagent;
        fifo_read_agent                           ragent;

        // Reference Model
        fifo_async_rm                             rm;

        // Scoreboard
        fifo_scoreboard                           scb;

        // FIFOs
        uvm_tlm_analysis_fifo#(fifo_write_tr)     drv_rm_wr_fifo;
        uvm_tlm_analysis_fifo#(fifo_read_tr)      drv_rm_rd_fifo;

        uvm_tlm_analysis_fifo#(fifo_write_mon_tr) duv_scb_wr_fifo;
        uvm_tlm_analysis_fifo#(fifo_read_mon_tr)  duv_scb_rd_fifo;

        uvm_tlm_analysis_fifo#(fifo_write_mon_tr) rm_scb_wr_fifo;
        uvm_tlm_analysis_fifo#(fifo_read_mon_tr)  rm_scb_rd_fifo;

        // Virtual sequencer
        fifo_virtual_sequencer                    vsqr;

        // Build phase
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);

            wagent          = fifo_write_agent::type_id::create("wagent", this);
            ragent          = fifo_read_agent::type_id::create("ragent", this);

            rm              = fifo_async_rm::type_id::create("rm", this);

            scb             = fifo_scoreboard::type_id::create("scb", this);

            drv_rm_wr_fifo  = new("drv_rm_wr_fifo", this);
            drv_rm_rd_fifo  = new("drv_rm_rd_fifo", this);
            duv_scb_wr_fifo = new("duv_scb_wr_fifo", this);
            duv_scb_rd_fifo = new("duv_scb_rd_fifo", this);
            rm_scb_wr_fifo  = new("rm_scb_wr_fifo", this);
            rm_scb_rd_fifo  = new("rm_scb_rd_fifo", this);

            vsqr            = fifo_virtual_sequencer::type_id::create("vsqr", this);
        endfunction : build_phase

        // Connect phase
        virtual function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);

            // Connect agent driver to reference model by FIFO
            wagent.drv_ap.connect(drv_rm_wr_fifo.analysis_export);
            ragent.drv_ap.connect(drv_rm_rd_fifo.analysis_export);

            rm.bgp_wr.connect(drv_rm_wr_fifo.blocking_get_export);
            rm.bgp_rd.connect(drv_rm_rd_fifo.blocking_get_export);

            // Connect agent monitor to scoreboard by FIFO
            wagent.mon_ap.connect(duv_scb_wr_fifo.analysis_export);
            ragent.mon_ap.connect(duv_scb_rd_fifo.analysis_export);

            scb.bgp_duv_wr.connect(duv_scb_wr_fifo.blocking_get_export);
            scb.bgp_duv_rd.connect(duv_scb_rd_fifo.blocking_get_export);

            // Connect reference model to scoreboard by FIFO
            rm.ap_wr.connect(rm_scb_wr_fifo.analysis_export);
            rm.ap_rd.connect(rm_scb_rd_fifo.analysis_export);

            scb.bgp_rm_wr.connect(rm_scb_wr_fifo.blocking_get_export);
            scb.bgp_rm_rd.connect(rm_scb_rd_fifo.blocking_get_export);

            // Give sequencer in agents to virtual sequencer
            vsqr.wr_sqr = wagent.sqr;
            vsqr.rd_sqr = ragent.sqr;

            `uvm_info(this.get_type_name(), "UVM components connected.", UVM_MEDIUM);
        endfunction : connect_phase
    endclass : fifo_verify_env
    
endpackage : hs_fifo_afifo_uvm_env_pkg