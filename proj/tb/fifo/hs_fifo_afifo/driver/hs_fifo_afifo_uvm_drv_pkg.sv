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
// FILE NAME: hs_fifo_afifo_uvm_drv_pkg.sv
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
// PURPOSE: Package of driver definition for UVM framework of hs_fifo_afifo
//
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE

// Package of driver definition for UVM framework of hs_fifo_afifo
package hs_fifo_afifo_uvm_drv_pkg;
    import uvm_pkg::*;
    import hs_ifr_misc_typedefs_pkg::*;
    import hs_fifo_afifo_uvm_param_pkg::*;
    import hs_fifo_afifo_uvm_seqitem_pkg::*;

    `include "uvm_macros.svh"

    class fifo_write_drv extends uvm_driver#(fifo_write_tr);
        `uvm_component_utils(fifo_write_drv)
        `uvm_new_func

        virtual hs_fifo_afifo_duv_if.wr   vif;

        uvm_analysis_port #(fifo_write_tr) rm_ap;

        // Build phase
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);

            if (!uvm_config_db#(virtual hs_fifo_afifo_duv_if.wr)::get(this, "", "vif", vif)) begin
                `uvm_fatal(get_type_name(), "Virtual interface has not configured");
            end

            rm_ap = new("rm_ap", this);
        endfunction : build_phase

        // Run phase
        virtual task run_phase(uvm_phase phase);
            vif.cb_wr.wvalid       <= '0;
            vif.cb_wr.wdata        <= '0;
            vif.cb_wr.wlast        <= '0;
            vif.cb_wr.wdrop        <= '0;

            @(posedge vif.src_aresetn); // Wait for reset released
            @(vif.cb_wr);
            forever begin
                fifo_write_tr tr;

                // Reset valid signal
                vif.cb_wr.wvalid       <= 1'b0;

                seq_item_port.get_next_item(tr);

                // Give the transaction to reference model)
                rm_ap.write(tr);

                // Wait for gap if needed
                vif.cb_wr.wvalid       <= 1'b0;
                repeat(tr.stall_cycle) @(vif.cb_wr);

                vif.cb_wr.wvalid       <= 1'b1;
                vif.cb_wr.wdata        <= tr.data;
                vif.cb_wr.wlast        <= tr.last;
                vif.cb_wr.wdrop        <= tr.drop;
                do @(vif.cb_wr);
                while (!vif.cb_wr.wready);

                seq_item_port.item_done();
            end
        endtask : run_phase
    endclass : fifo_write_drv

    class fifo_read_drv extends uvm_driver#(fifo_read_tr);
        `uvm_component_utils(fifo_read_drv)
        `uvm_new_func

        virtual hs_fifo_afifo_duv_if.rd  vif;

        uvm_analysis_port #(fifo_read_tr
        ) rm_ap;

        // Build phase
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);

            if (!uvm_config_db#(virtual hs_fifo_afifo_duv_if.rd)::get(this, "", "vif", vif)) begin
                `uvm_fatal(get_type_name(), "Virtual interface has not configured");
            end

            rm_ap = new("rm_ap", this);
        endfunction : build_phase

        // Run phase
        virtual task run_phase(uvm_phase phase);
            vif.cb_rd.rready <= '0;

            @(posedge vif.dst_aresetn); // Wait for reset released
            @(vif.cb_rd);

            forever begin
                fifo_read_tr tr;

                // Reset ready signal
                vif.cb_rd.rready <= 1'b0;

                seq_item_port.get_next_item(tr);

                // Give the transaction to reference model
                rm_ap.write(tr);

                // Wait for gap if needed
                vif.cb_rd.rready <= 1'b0;
                repeat (tr.stall_cycle) @(vif.cb_rd);

                if (EN_PACKET_MODE == BOOL_FALSE) begin
                    // Normal read mode

                    vif.cb_rd.rready <= 1'b1;
                    do @(vif.cb_rd);
                    while (!vif.cb_rd.rvalid);
                end
                else begin
                    // Packet mode

                    // After the gap, start the packet read
                    // We need read the packet until the last signal
                    // Also, during the packet read, we need to hold the peek signal
                    vif.cb_rd.rready <= 1'b1;
                    do @(vif.cb_rd);
                    while (!(vif.cb_rd.rvalid && vif.cb_rd.rlast));
                end

                seq_item_port.item_done();
            end
        endtask : run_phase
    endclass : fifo_read_drv
endpackage : hs_fifo_afifo_uvm_drv_pkg