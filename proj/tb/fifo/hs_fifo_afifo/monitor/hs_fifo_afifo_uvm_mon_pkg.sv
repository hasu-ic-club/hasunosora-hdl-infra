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
// FILE NAME: hs_fifo_afifo_uvm_mon_pkg.sv
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
// PURPOSE: 
//
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

package hs_fifo_afifo_uvm_mon_pkg;
    import uvm_pkg::*;
    import hs_ifr_misc_typedefs_pkg::*;
    import hs_fifo_afifo_uvm_param_pkg::*;
    import hs_fifo_afifo_uvm_seqitem_pkg::*;

    `include "uvm_macros.svh"

    class fifo_write_mon extends uvm_monitor;
        virtual hs_fifo_afifo_duv_if.wr      vif;

        uvm_analysis_port#(fifo_write_mon_tr) ap;

        `uvm_component_utils(fifo_write_mon)
        `uvm_new_func

        // Build phase
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);

            if (!uvm_config_db#(virtual hs_fifo_afifo_duv_if.wr)::get(this, "", "vif", vif)) begin
                `uvm_fatal(get_type_name(), "Virtual interface has not configured");
            end

            ap         = new("ap", this);
        endfunction : build_phase

        // Run phase
        task run_phase(uvm_phase phase);
            @(posedge vif.src_aresetn); // Wait for reset released

            forever begin
                @(vif.cb_wr);

                if (vif.cb_wr_mon.wvalid_i && vif.cb_wr_mon.wready) begin
                    fifo_write_mon_tr tr      = fifo_write_mon_tr::type_id::create("wr_mon");

                    tr.data                   = vif.cb_wr_mon.wdata_i;
                    tr.last                   = vif.cb_wr_mon.wlast_i;
                    tr.drop                   = vif.cb_wr_mon.wdrop_i;

                    ap.write(tr);
                end
            end
        endtask : run_phase
    endclass : fifo_write_mon


    class fifo_read_mon extends uvm_monitor;
        virtual hs_fifo_afifo_duv_if.rd     vif;

        uvm_analysis_port#(fifo_read_mon_tr) ap;

        `uvm_component_utils(fifo_read_mon)
        `uvm_new_func

        // Build phase
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);

            if (!uvm_config_db#(virtual hs_fifo_afifo_duv_if.rd)::get(this, "", "vif", vif)) begin
                `uvm_fatal(get_type_name(), "Virtual interface has not configured");
            end

            ap = new("ap", this);
        endfunction : build_phase

        // Run phase
        task run_phase(uvm_phase phase);
            @(posedge vif.dst_aresetn); // Wait for reset released

            forever begin
                @(vif.cb_rd);

                if (vif.cb_rd_mon.rvalid && vif.cb_rd_mon.rready_i) begin
                    fifo_read_mon_tr tr        = fifo_read_mon_tr::type_id::create("rd_mon");

                    tr.data                    = vif.cb_rd_mon.rdata;
                    tr.last                    = vif.cb_rd_mon.rlast;

                    ap.write(tr);
                end
            end
        endtask : run_phase
    endclass : fifo_read_mon
endpackage : hs_fifo_afifo_uvm_mon_pkg