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
// FILE NAME: hs_fifo_sfifo_uvm_scb_pkg.sv
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
// PURPOSE: Package of scoreboard definition for UVM framework of hs_fifo_sfifo
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// N/A
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE

// Package of scoreboard definition for UVM framework of hs_fifo_sfifo
package hs_fifo_sfifo_uvm_scb_pkg;
    import uvm_pkg::*;
    import hs_ifr_misc_typedefs_pkg::*;
    import hs_fifo_sfifo_uvm_seqitem_pkg::*;

    `include "uvm_macros.svh"

    class fifo_scoreboard extends uvm_scoreboard;

        uvm_blocking_get_port#(fifo_write_mon_tr) bgp_rm_wr;
        uvm_blocking_get_port#(fifo_write_mon_tr) bgp_duv_wr;

        uvm_blocking_get_port#(fifo_read_mon_tr)  bgp_rm_rd;
        uvm_blocking_get_port#(fifo_read_mon_tr)  bgp_duv_rd;

        bit                                       wside_thread_wait;
        bit                                       rside_thread_wait;

        int                                       wside_error;
        int                                       rside_error;

        `uvm_component_utils(fifo_scoreboard)
        `uvm_new_func

        // Build phase
        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);

            bgp_rm_wr         = new("bgp_rm_wr", this);
            bgp_duv_wr        = new("bgp_duv_wr", this);

            bgp_rm_rd         = new("bgp_rm_rd", this);
            bgp_duv_rd        = new("bgp_duv_rd", this);

            wside_thread_wait = 1;
            rside_thread_wait = 1;

            wside_error       = 0;
            rside_error       = 0;
        endfunction : build_phase

        // Run phase
        virtual task run_phase(uvm_phase phase);
            super.run_phase(phase);

            fork
                write_side_scb();
                read_side_scb();
            join
        endtask : run_phase

        // Report phase
        virtual function void report_phase(uvm_phase phase);
            super.report_phase(phase);

            if ((wside_error != 0) || (rside_error != 0)) begin
                `uvm_fatal(this.get_type_name(), $sformatf("Test FAILED with %0d write side error(s) and %0d read side error(s).", wside_error, rside_error));
            end
        endfunction : report_phase

        function bit is_all_scb_done;
            // If both write and read side are waiting for transaction,
            // but the TLM FIFO is all empty
            // The Scoreboard is done
            return (wside_thread_wait && rside_thread_wait);
        endfunction

        task write_side_scb;
            forever begin
                fifo_write_mon_tr rm_exp, duv_act;
                string exception_why;

                fork
                    bgp_rm_wr.get(rm_exp);
                    bgp_duv_wr.get(duv_act);
                join
                wside_thread_wait = 0;

                if(write_side_equal_chk(rm_exp, duv_act, exception_why)) begin
                    `uvm_error(get_type_name(), $sformatf("WR SCB ERROR: %s", exception_why));
                    wside_error++;
                end
                wside_thread_wait = 1;
            end
        endtask : write_side_scb

        task read_side_scb;
            forever begin
                fifo_read_mon_tr rm_exp, duv_act;
                string exception_why;

                fork
                    bgp_rm_rd.get(rm_exp);
                    bgp_duv_rd.get(duv_act);
                join

                rside_thread_wait = 0;

                if (read_side_equal_chk(rm_exp, duv_act, exception_why)) begin
                    `uvm_error(get_type_name(), $sformatf("RD SCB ERROR: %s", exception_why));
                    rside_error++;
                end

                rside_thread_wait = 1;
            end
        endtask : read_side_scb

        function bit write_side_equal_chk(fifo_write_mon_tr rm_exp, fifo_write_mon_tr duv_act, output string why);
            if (rm_exp.level != duv_act.level) begin
                why = $sformatf("FIFO level expected(RM) = %0d, actual(DUV) = %0d", rm_exp.level, duv_act.level);
                return 1;
            end

            if (rm_exp.almost_full != duv_act.almost_full) begin
                why = $sformatf("Almost Full expected(RM) = %0d, actual(DUV) = %0d", rm_exp.almost_full, duv_act.almost_full);
                return 1;
            end

            return 0;
        endfunction : write_side_equal_chk

        function bit read_side_equal_chk(fifo_read_mon_tr rm_exp, fifo_read_mon_tr duv_act, output string why);

            if (rm_exp.level != duv_act.level) begin
                why = $sformatf("FIFO level expected(RM) = %0d, actual(DUV) = %0d", rm_exp.level, duv_act.level);
                return 1;
            end

            if (rm_exp.data != duv_act.data) begin
                why = $sformatf("Data expected(RM) = %0h, actual(DUV) = %0h", rm_exp.data, duv_act.data);
                return 1;
            end


            if (rm_exp.last != duv_act.last) begin
                why = $sformatf("Last Signal expected(RM) = %0d, actual(DUV) = %0d", rm_exp.last, duv_act.last);
                return 1;
            end

            if (rm_exp.almost_empty != duv_act.almost_empty) begin
                why = $sformatf("Almost Empty expected(RM) = %0d, actual(DUV) = %0d", rm_exp.almost_empty, duv_act.almost_empty);
                return 1;
            end

            return 0;
        endfunction : read_side_equal_chk
    endclass
endpackage : hs_fifo_sfifo_uvm_scb_pkg