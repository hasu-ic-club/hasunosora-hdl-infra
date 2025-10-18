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
// FILE NAME: hs_fifo_afifo_uvm_rm_pkg.sv
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
// PURPOSE: Package of reference model definition for UVM framework of hs_fifo_afifo
//
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE


// Package of reference model definition for UVM framework of hs_fifo_afifo
package hs_fifo_afifo_uvm_rm_pkg;
    import uvm_pkg::*;
    import hs_ifr_misc_typedefs_pkg::*;
    import hs_fifo_afifo_uvm_param_pkg::*;
    import hs_fifo_afifo_uvm_seqitem_pkg::*;

    `include "uvm_macros.svh"

    class fifo_async_rm extends uvm_component;
        // Driver ports
        uvm_blocking_get_port#(fifo_write_tr)   bgp_wr;
        uvm_blocking_get_port#(fifo_read_tr)    bgp_rd;

        // Monitor ports
        uvm_analysis_port#(fifo_write_mon_tr)   ap_wr;
        uvm_analysis_port#(fifo_read_mon_tr)    ap_rd;

        `uvm_component_utils(fifo_async_rm)
        `uvm_new_func

        // Simulated FIFO
        typedef struct packed
        {
            bit       last;
            DATA_TYPE data;
        } fifo_data_s;

        mailbox#(fifo_data_s)                   fifo_q;
        fifo_data_s                             wpkt_fifo_q[$];

        // Build phase
        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);

            bgp_wr    = new("bgp_wr", this);
            bgp_rd    = new("bgp_rd", this);
            ap_wr     = new("ap_wr", this);
            ap_rd     = new("ap_rd", this);

            fifo_q = new();
        endfunction : build_phase

        // Run phase
        virtual task run_phase(uvm_phase phase);
            fifo_write_tr     wr_tr;
            fifo_read_tr      rd_tr;

            fifo_write_mon_tr wr_mon;
            fifo_read_mon_tr  rd_mon;

            fork
                forever begin : rd_side
                    bit pkt_last;
                    fifo_data_s data_rd;

                    bgp_rd.get(rd_tr);

                    if (EN_PACKET_MODE == BOOL_FALSE) begin
                        fifo_q.get(data_rd);

                        rd_mon      = fifo_read_mon_tr::type_id::create("rd_mon");
                        rd_mon.data = data_rd.data;
                        rd_mon.last = data_rd.last;

                        ap_rd.write(rd_mon);

                        `uvm_info(get_type_name(), $sformatf("RM: (Read) A transaction done. Data=%0h, Last=%0b",
                                rd_mon.data, rd_mon.last), UVM_HIGH);

                    end
                    else begin
                        // In packet mode
                        do begin
                            fifo_q.get(data_rd);

                            rd_mon      = fifo_read_mon_tr::type_id::create("rd_mon");
                            rd_mon.data = data_rd.data;
                            rd_mon.last = data_rd.last;
                            
                            ap_rd.write(rd_mon);

                            `uvm_info(get_type_name(), $sformatf("RM: (Read) A transaction done. Data=%0h, Last=%0b",
                                    rd_mon.data, rd_mon.last), UVM_HIGH);

                            pkt_last = data_rd.last;
                        end
                        while (!pkt_last);     
                    end
                end : rd_side
                forever begin : wr_side
                    fifo_data_s data_wr;

                    wr_mon              = fifo_write_mon_tr::type_id::create("wr_mon");

                    bgp_wr.get(wr_tr);

                    data_wr.data        = wr_tr.data;
                    data_wr.last        = wr_tr.last;

                    if (EN_PACKET_MODE == BOOL_FALSE) begin
                        fifo_q.put(data_wr);
                    end
                    else begin
                        // In packet mode, we should write the data to a 'non-full packet' queue
                        // Then move the data to FIFO queue when we see the last signal
                        // If user drop the packet, we can simply clear the 'non-full packet' queue
                        if (wr_tr.drop) begin
                            clear_non_full_pkt();
                        end
                        else begin
                            wpkt_fifo_q.push_back(data_wr);

                            if (wr_tr.last) begin
                                mov_full_pkt_to_queue();
                            end
                        end
                    end

                    wr_mon.data         = wr_tr.data;
                    wr_mon.last         = wr_tr.last;
                    wr_mon.drop         = wr_tr.drop;

                    ap_wr.write(wr_mon);

                    `uvm_info(get_type_name(), $sformatf("RM: (Write) A transaction done. Data=%0h, Last=%0b, Drop=%0b",
                            wr_mon.data, wr_mon.last, wr_mon.drop), UVM_HIGH);
                end : wr_side
            join
        endtask : run_phase


        task mov_full_pkt_to_queue;
            int how_many_data = wpkt_fifo_q.size();
            for (int item = 0; item < how_many_data; item++) begin
                fifo_q.put(wpkt_fifo_q.pop_front());
            end
        endtask

        task clear_non_full_pkt;
            int how_many_data = wpkt_fifo_q.size();

            for (int item = 0; item < how_many_data; item++) begin
                void'(wpkt_fifo_q.pop_front());
            end
        endtask
    endclass : fifo_async_rm
endpackage : hs_fifo_afifo_uvm_rm_pkg