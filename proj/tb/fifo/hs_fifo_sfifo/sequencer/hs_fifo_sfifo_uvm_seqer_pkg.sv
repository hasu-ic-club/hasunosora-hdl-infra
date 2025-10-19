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
// FILE NAME: hs_fifo_sfifo_uvm_seqer_pkg.sv
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
// PURPOSE: Package of sequencer definition for UVM framework of hs_fifo_sfifo
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// N/A
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE

// Package of sequencer definition for UVM framework of hs_fifo_sfifo
package hs_fifo_sfifo_uvm_seqer_pkg;
    import uvm_pkg::*;
    import hs_ifr_misc_typedefs_pkg::*;
    import hs_fifo_sfifo_uvm_param_pkg::*;
    import hs_fifo_sfifo_uvm_seqitem_pkg::*;
    import hs_fifo_sfifo_uvm_seq_pkg::*;

    `include "uvm_macros.svh"

    class fifo_write_sequencer extends uvm_sequencer#(fifo_write_tr);
        `uvm_component_utils(fifo_write_sequencer)
        `uvm_new_func
    endclass : fifo_write_sequencer


    class fifo_read_sequencer extends uvm_sequencer#(fifo_read_tr);
        `uvm_component_utils(fifo_read_sequencer)
        `uvm_new_func
    endclass : fifo_read_sequencer

    class fifo_virtual_sequencer extends uvm_sequencer;

        `uvm_component_utils(fifo_virtual_sequencer)
        `uvm_new_func

        fifo_write_sequencer wr_sqr;
        fifo_read_sequencer  rd_sqr;
    endclass : fifo_virtual_sequencer


    class fifo_virtual_seq extends uvm_sequence;
        `uvm_object_utils(fifo_virtual_seq)
        `uvm_declare_p_sequencer(fifo_virtual_sequencer)

        function new(string name="v_seq");
            super.new(name);
        endfunction : new

        // Pre-body
        virtual task pre_body();
            super.pre_body();

            if (starting_phase) begin
                starting_phase.raise_objection(this, "top virtual sequence start");
                `uvm_info(this.get_type_name(), "Objection raised", UVM_LOW);
            end
            else begin
                `uvm_info(this.get_type_name(), "Starting phase is empty, can not raise the objection", UVM_LOW);
            end
        endtask : pre_body

        // Post body
        virtual task post_body();
            if (starting_phase) begin
                starting_phase.drop_objection(this, "top virtual sequence done");
                `uvm_info(this.get_type_name(), "Objection dropped", UVM_LOW);
            end

            super.post_body();
        endtask : post_body

        virtual task body();
            int                  case_limit;

            fifo_write_base_seq  wrseq;
            fifo_burst_read_seq  rdseq      = fifo_burst_read_seq::type_id::create("rdseq");

            if (EN_PACKET_MODE == BOOL_TRUE) begin
                wrseq = fifo_package_write_seq::type_id::create("wrseq_pkg");
            end
            else begin
                wrseq = fifo_burst_write_seq::type_id::create("wrseq_burst");
            end

            // Get case limit
            if (!uvm_config_db#(int)::get(null, get_full_name(), "case_limit", case_limit)) begin
                case_limit = 1;
                `uvm_warning(this.get_type_name(), "Caselimit configuration is not in config_db, set to 1");
            end

            wrseq.n_beats = case_limit;
            rdseq.n_beats = case_limit;

            fork
                wrseq.start(p_sequencer.wr_sqr);
                rdseq.start(p_sequencer.rd_sqr);
            join_any
        endtask : body
    endclass : fifo_virtual_seq
endpackage : hs_fifo_sfifo_uvm_seqer_pkg