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
// FILE NAME: hs_fifo_sfifo_uvm_agent_pkg.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a0
// VERSION DESCRIPTION: First Edition
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/9/15     First Edition
//-------------------------------------------------------------------------
// PURPOSE: Package of agent definition for UVM framework of hs_fifo_sfifo
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// N/A
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// Package of agent definition for UVM framework of hs_fifo_sfifo
package hs_fifo_sfifo_uvm_agent_pkg;
    import uvm_pkg::*;
    import hs_ifr_misc_typedefs_pkg::*;
    import hs_fifo_sfifo_uvm_param_pkg::*;
    import hs_fifo_sfifo_uvm_seqitem_pkg::*;
    import hs_fifo_sfifo_uvm_seqer_pkg::*;
    import hs_fifo_sfifo_uvm_drv_pkg::*;
    import hs_fifo_sfifo_uvm_mon_pkg::*;

    `include "uvm_macros.svh"

    class fifo_write_agent extends uvm_agent;

        virtual hs_fifo_sfifo_duv_if.wr      vif;

        fifo_write_sequencer                  sqr;

        fifo_write_drv                        drv;

        fifo_write_mon                        mon;

        uvm_analysis_port#(fifo_write_tr)     drv_ap;
        uvm_analysis_port#(fifo_write_mon_tr) mon_ap;

        `uvm_component_utils(fifo_write_agent)
        `uvm_new_func

        // Build phase
        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);

            if (!uvm_config_db#(virtual hs_fifo_sfifo_duv_if.wr)::get(this, "", "vif", vif)) begin
                `uvm_fatal(get_type_name(), "Virtual interface has not configured");
            end

            drv = new("drv", this);
            mon = new("mon", this);
            sqr = new("sqr", this);
        endfunction : build_phase

        // Connect phase
        function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);

            // Connect driver to sequencer
            drv.seq_item_port.connect(sqr.seq_item_export);

            // Connect APs to self APs
            drv_ap = drv.rm_ap;
            mon_ap = mon.ap;
        endfunction : connect_phase
    endclass : fifo_write_agent

    class fifo_read_agent extends uvm_agent;

        virtual hs_fifo_sfifo_duv_if.rd     vif;

        fifo_read_sequencer                  sqr;
        fifo_read_drv                        drv;
        fifo_read_mon                        mon;

        uvm_analysis_port#(fifo_read_tr)     drv_ap;
        uvm_analysis_port#(fifo_read_mon_tr) mon_ap;

        `uvm_component_utils(fifo_read_agent)
        `uvm_new_func

        // Build phase
        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);

            if (!uvm_config_db#(virtual hs_fifo_sfifo_duv_if.rd)::get(this, "", "vif", vif)) begin
                `uvm_fatal(get_type_name(), "Virtual interface has not configured");
            end

            drv = new("drv", this);
            mon = new("mon", this);
            sqr = new("sqr", this);
        endfunction : build_phase

        // Connect phase
        function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);

            // Connect driver to sequencer
            drv.seq_item_port.connect(sqr.seq_item_export);

            // Connect APs to self APs
            drv_ap = drv.rm_ap;
            mon_ap = mon.ap;
        endfunction : connect_phase
    endclass : fifo_read_agent
endpackage : hs_fifo_sfifo_uvm_agent_pkg