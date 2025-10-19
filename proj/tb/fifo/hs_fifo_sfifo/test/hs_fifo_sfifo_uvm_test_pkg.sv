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
// FILE NAME: hs_fifo_sfifo_uvm_test_pkg.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a0
// VERSION DESCRIPTION: First Edition
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/9/16     First Edition
//-------------------------------------------------------------------------
// PURPOSE: Package of test definition for UVM framework of hs_fifo_sfifo
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// N/A
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE

// Package of test definition for UVM framework of hs_fifo_sfifo
package hs_fifo_sfifo_uvm_test_pkg;
    import uvm_pkg::*;
    import hs_ifr_misc_typedefs_pkg::*;
    import hs_fifo_sfifo_uvm_param_pkg::*;
    import hs_fifo_sfifo_uvm_seqer_pkg::*;
    import hs_fifo_sfifo_uvm_env_pkg::*;

    `include "uvm_macros.svh"

    class fifo_burst_test extends uvm_test;
        `uvm_component_utils(fifo_burst_test)
        `uvm_new_func

        fifo_verify_env env;

        // Build phase
        virtual function void build_phase(uvm_phase phase);
            int case_limit = 1000;
            if ($value$plusargs("UVM_CASELIMIT=%d", case_limit)) begin
                `uvm_info(this.get_type_name(), $sformatf("Case limit per sequence set to %0d", case_limit), UVM_LOW);
            end

            uvm_config_db #(int)::set(this, "*", "case_limit", case_limit);

            env  = new("env", this);

            super.build_phase(phase);
        endfunction : build_phase

        // Connect phase
        virtual function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);
        endfunction : connect_phase

        virtual function void report_phase(uvm_phase phase);
            super.report_phase(phase);
            
            `uvm_info(this.get_type_name(), "Test done.", UVM_MEDIUM);
        endfunction : report_phase

        // Run phase
        virtual task run_phase(uvm_phase phase);
            fifo_virtual_seq vseq = new("vseq");

            vseq.starting_phase = phase;
            vseq.start(env.vsqr);
        endtask : run_phase
    endclass : fifo_burst_test
endpackage : hs_fifo_sfifo_uvm_test_pkg