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
// FILE NAME: hs_fifo_sfifo_uvm_rm_pkg.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a0
// VERSION DESCRIPTION: First Edition
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/9/13     First Edition
//-------------------------------------------------------------------------
// PURPOSE: Package of reference model definition for UVM framework of
//   hs_fifo_sfifo
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// N/A
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE

// Package of reference model definition for UVM framework of hs_fifo_sfifo
package hs_fifo_sfifo_uvm_rm_pkg;
    import uvm_pkg::*;
    import hs_math_basic_pkg::*;
    import hs_ifr_misc_typedefs_pkg::*;
    import hs_fifo_sfifo_uvm_param_pkg::*;
    import hs_fifo_sfifo_uvm_seqitem_pkg::*;

    `include "uvm_macros.svh"

    class fifo_refmodel;
        localparam int       FIFO_REAL_DEPTH        = (EN_OUTPUT_REG == BOOL_TRUE) ? (FIFO_DEPTH + 1) : FIFO_DEPTH;

        typedef struct packed
        {
            bit       last;
            DATA_TYPE data;
        } fifo_data_s;

        // FIFO
        fifo_data_s          fifo_q[$];

        // Output register
        fifo_data_s          out_reg;
        bit                  out_reg_not_empty;
        bit                  out_reg_rd_done;
        int                  out_reg_lvl;
        bit                  out_reg_pkt_last;

        bit                  need_read;

        // Pessimistic estimation of the packet
        bit                  no_full_pkt_est;
        bit                  no_full_pkt_est_dly;

        // Real level and packet level
        int                  level;

        // Level as seen from read side
        // That is, the write transaction has a latency of 1 cycle
        // to read side
        int                  rside_level;
        int                  rside_pkt_level;
        int                  rside_pkt_level_reg;

        // The pointer for peek the packet
        int                  peek_pointer;

        // Indicate there is a completed transaction in the current cycle
        bit                  rd_done;
        bit                  wr_done;

        bit            [1:0] wr_done_dly;

        bit                  pkt_wr_done;
        bit                  pkt_rd_done;

        bit            [1:0] pkt_wr_done_dly;

        int                  item_dropped;

        bit                  not_empty;
        bit                  not_empty_pre;
        bit                  not_full;
        bit                  almost_empty;
        bit                  almost_full;

        function new();
            not_full     = 1;
            almost_empty = 1;
        endfunction : new

        task tick();
            // Prepare for values in this cycle
            if ((EN_PACKET_MODE == BOOL_TRUE) && (EN_OUTPUT_REG == BOOL_TRUE)) begin
                no_full_pkt_est     = out_reg.last && out_reg_not_empty && (rside_pkt_level <= 1) && out_reg_rd_done;

                not_empty           = not_empty && !no_full_pkt_est && !no_full_pkt_est_dly;
            end

            // Prepare for values in next cycle

            // Processing the output register
            if (EN_OUTPUT_REG == BOOL_TRUE) begin
                out_reg_lvl         = 0;
                if (!out_reg_not_empty || out_reg_rd_done) begin

                    // If the output register read a data but not output
                    // Record the data level in this cycle
                    if (not_empty && !out_reg_rd_done) begin
                        out_reg_lvl       = 1;
                    end
                    // If the output register output but can not read new data
                    // from the FIFO, the recorded data level need to be
                    // cleared
                    else if (!not_empty && out_reg_rd_done) begin
                        out_reg_lvl       = -1;
                    end
                    else begin
                        out_reg_lvl       = 0;
                    end


                    if (not_empty) begin
                        read(0, out_reg.data, out_reg.last);
                        out_reg_not_empty = 1;
                    end
                    else begin
                        out_reg_not_empty = 0;
                    end
                end

                out_reg_rd_done     = 0;
            end

            no_full_pkt_est_dly = no_full_pkt_est;

            // Collect operations in this cycle
            // Buffer the write done flag
            wr_done_dly         = {wr_done_dly[0], wr_done};
            pkt_wr_done_dly     = {pkt_wr_done_dly[0], pkt_wr_done};

            level               = level + wr_done - rd_done - item_dropped + out_reg_lvl;

            rside_level         = rside_level + wr_done_dly[1] - rd_done - item_dropped;
            rside_pkt_level     = rside_pkt_level + pkt_wr_done_dly[1] - pkt_rd_done;

            if (EN_PACKET_MODE == BOOL_TRUE) begin
                // This variable is used for 'read_valid_ram_pre' in RTL design
                // Beacuse the not_empty signal is not read directly from verification side
                if (EN_OUTPUT_REG == BOOL_TRUE) begin
                    not_empty = rside_pkt_level_reg > 0;
                end
                else begin
                    not_empty = rside_pkt_level > 0;
                end
            end
            else begin
                not_empty           = rside_level > 0;
            end

            not_full            = level < FIFO_REAL_DEPTH;

            rside_pkt_level_reg = rside_pkt_level;

            almost_full         = (ALMOST_FULL_LVL == FIFO_DEPTH) ? !not_full : (level >= ALMOST_FULL_LVL);
            if (EN_OUTPUT_REG == BOOL_FALSE) begin
                almost_empty        = (ALMOST_EMPTY_LVL == 0) ? !not_empty : (level <= ALMOST_EMPTY_LVL);
            end
            else begin
                almost_empty        = (ALMOST_EMPTY_LVL == 0) ? !out_reg_not_empty : (level <= ALMOST_EMPTY_LVL);
            end

            // Reset all flags for next cycle
            item_dropped        = 0;
            rd_done             = 0;
            wr_done             = 0;
            pkt_wr_done         = 0;
            pkt_rd_done         = 0;
        endtask : tick

        task write(input DATA_TYPE item, input bit last);
            fifo_data_s wrin;
            wrin.data = item;
            wrin.last = last;

            assert(fifo_q.size() <= FIFO_REAL_DEPTH)
            else $fatal(1, "FIFO Reference Model: Assertion Failed::Overflow");

            fifo_q.push_back(wrin);
            wr_done   = 1;

            if ((EN_PACKET_MODE == BOOL_TRUE) && (wrin.last)) begin
                pkt_wr_done = 1;
            end
        endtask : write

        task read(input bit peek, output DATA_TYPE item, output bit last);
            fifo_data_s rdout;

            assert (fifo_q.size() > 0)
            else $fatal(1, "FIFO Reference Model: Assertion Failed::Underflow");

            if (peek) begin
                rdout       = fifo_q[peek_pointer];
                peek_pointer++;

                if (rdout.last) begin
                    peek_pointer = 0;
                end
            end
            else begin
                rdout       = fifo_q.pop_front();
                rd_done     = 1;
            end

            if ((EN_PACKET_MODE == BOOL_TRUE) && (EN_OUTPUT_REG == BOOL_FALSE) && (rdout.last) && (!peek)) begin
                pkt_rd_done = 1;
            end

            item = rdout.data;
            last = rdout.last;
        endtask : read

        task read_from_out_reg(output DATA_TYPE item, output bit last);
            fifo_data_s rdout;

            if (EN_OUTPUT_REG == BOOL_FALSE) begin
                $fatal(1, "FIFO Reference Model: Assertion Failed::Output Register Not Enabled");
            end

            assert (out_reg_not_empty)
            else $fatal(1, "FIFO Reference Model: Assertion Failed::Underflow");

            rdout           = out_reg;
            out_reg_rd_done = 1;

            if ((EN_PACKET_MODE == BOOL_TRUE) && (rdout.last)) begin
                pkt_rd_done = 1;
            end

            item            = rdout.data;
            last            = rdout.last;
        endtask : read_from_out_reg

        task drop();
            fifo_data_s item;

            // Drop packet
            assert(EN_DROP_PACKET == BOOL_TRUE)
            else $fatal(1, "FIFO Reference Model: Assertion Failed::Drop Packet Not Supported");

            if (fifo_q.size() <= 0) return;

            // There are 3 saturation to drop
            // 1. A packet is being written, but not yet completed
            //    --- Previous Packet --- LAST | --- New Packet ---...
            //                                    ^ This packet is being dropped
            // 2. A packet is fully written, but not yet read
            //    --- Previous Packet --- LAST | ///// Nothing
            ///       ^ This packet is being dropped
            // 3. A packet is begin written, and the LAST signal meets in the same cycle
            //    --- Previous Packet --- LAST | --- New Packet --- LAST |
            //                                    ^ This packet is being dropped

            // In case 1 and 3, we need to found the 1st LAST signal, remove all items after it;
            // In case 2, we need to found the 2nd LAST signal, remove all items after it;
            // That is, we need to drop at least one data from queue, and continue to drop until
            // a LAST signal is found

            item         = fifo_q.pop_back();
            item_dropped++;

            // If the FIFO has only one item, it must be the case 1 or 3
            if (fifo_q.size() > 0) begin
                do begin
                    item = fifo_q.pop_back();
                    item_dropped++;
                end while (fifo_q.size() > 0 && !item.last);

                // If the final item is a LAST item (That is we exit the loop due to finding a LAST item)
                // We need to refill the LAST item back to the FIFO,
                // because this item is a part of the previous packet
                if (item.last) begin
                    fifo_q.push_back(item);
                    item_dropped--;
                end
            end

            // If any packet's last write in the same cycle as the drop
            // The packet is considered as gived up
            // So the packet level should not be increased
            pkt_wr_done  = 0;
        endtask : drop
    endclass : fifo_refmodel

    class fifo_norm_rm extends uvm_component;

        // Driver ports
        uvm_nonblocking_get_port#(fifo_write_tr)bgp_wr;
        uvm_nonblocking_get_port#(fifo_read_tr) bgp_rd;

        // Monitor ports
        uvm_analysis_port#(fifo_write_mon_tr)   ap_wr;
        uvm_analysis_port#(fifo_read_mon_tr)    ap_rd;

        `uvm_component_utils(fifo_norm_rm)
        `uvm_new_func

        virtual hs_fifo_sfifo_duv_if           vif;
        fifo_refmodel                           ref_model;

        // Build phase
        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);

            bgp_wr    = new("bgp_wr", this);
            bgp_rd    = new("bgp_rd", this);
            ap_wr     = new("ap_wr", this);
            ap_rd     = new("ap_rd", this);

            // Get virutal interface
            if (!uvm_config_db#(virtual hs_fifo_sfifo_duv_if)::get(this, "", "vif", vif)) begin
                `uvm_fatal(get_type_name(), "Virtual interface has not configured");
            end

            ref_model = new();
        endfunction : build_phase

        virtual task run_phase(uvm_phase phase);
            fifo_write_tr     wr_tr;
            fifo_read_tr      rd_tr;

            fifo_write_mon_tr wr_mon;
            fifo_read_mon_tr  rd_mon;

            bit               pending_write    = 0;
            bit               pending_read     = 0;
            bit               wr_pending_rslv  = 0;
            bit               rd_pending_rslv  = 0;
            bit               rd_packet_over   = 0;
            int               rd_stall_cycle   = 0;
            int               wr_stall_cycle   = 0;

            forever begin
                wr_mon              = fifo_write_mon_tr::type_id::create("wr_mon");
                rd_mon              = fifo_read_mon_tr::type_id::create("rd_mon");

                @(posedge vif.clk);

                if (!pending_write) begin
                    if (bgp_wr.try_get(wr_tr)) begin
                        pending_write       = 1;
                        wr_stall_cycle      = wr_tr.stall_cycle;
                    end
                end

                if (!pending_read) begin
                    if (bgp_rd.try_get(rd_tr)) begin
                        pending_read        = 1;
                        rd_stall_cycle      = rd_tr.stall_cycle;
                        rd_packet_over      = 0;
                    end
                end

                if (!pending_write && !pending_read) begin
                    continue;
                end

                if (pending_read) begin
                    if (rd_stall_cycle == 0) begin
                        if (EN_OUTPUT_REG == BOOL_TRUE) begin
                            ref_model.need_read = 1;
                            if (ref_model.out_reg_not_empty) begin
                                ref_model.read_from_out_reg(rd_mon.data, rd_mon.last);
                                rd_mon.peek         = rd_tr.peek;
                                rd_pending_rslv     = 1;
                                rd_packet_over      = rd_mon.last;
                            end
                        end
                        else begin
                            if (ref_model.not_empty) begin
                                ref_model.read(rd_tr.peek, rd_mon.data, rd_mon.last);
                                rd_mon.peek         = rd_tr.peek;
                                rd_pending_rslv     = 1;
                                rd_packet_over      = rd_mon.last;
                            end
                        end
                    end
                    else begin
                        ref_model.need_read = 0;
                        rd_stall_cycle--;
                    end
                end

                if (pending_write) begin
                    if (wr_stall_cycle == 0) begin
                        if (ref_model.not_full) begin
                            ref_model.write(wr_tr.data, wr_tr.last);

                            wr_pending_rslv     = 1;
                        end

                        if (wr_tr.drop) begin
                            ref_model.drop();
                        end

                        wr_mon.data         = wr_tr.data;
                        wr_mon.last         = wr_tr.last;
                        wr_mon.drop         = wr_tr.drop;
                    end
                    else begin
                        wr_stall_cycle--;
                    end
                end

                wr_mon.almost_full  = ref_model.almost_full;
                wr_mon.level        = ref_model.level;
                rd_mon.almost_empty = ref_model.almost_empty;
                rd_mon.level        = ref_model.level;

                if (pending_write && wr_pending_rslv) begin
                    ap_wr.write(wr_mon);
                    `uvm_info(get_type_name(), $sformatf("RM: (Write) A transaction done. Data=%0h, Last=%0b, Drop=%0b, Almost_Full=%0b, Level=%0d",
                            wr_mon.data, wr_mon.last, wr_mon.drop, wr_mon.almost_full, wr_mon.level), UVM_HIGH);
                end

                if (pending_read && rd_pending_rslv) begin
                    ap_rd.write(rd_mon);
                    `uvm_info(get_type_name(), $sformatf("RM: (Read) A transaction done. Data=%0h, Last=%0b, Peek=%0b, Almost_Empty=%0b, Level=%0d",
                            rd_mon.data, rd_mon.last, rd_mon.peek, rd_mon.almost_empty, rd_mon.level), UVM_HIGH);
                end

                if (wr_pending_rslv) begin
                    pending_write       = 0;
                    wr_pending_rslv     = 0;
                end

                if (rd_pending_rslv) begin
                    if (EN_PACKET_MODE == BOOL_FALSE) begin
                        pending_read        = 0;
                    end
                    else begin
                        // In packet mode, the pending read will be cleared only when the packet is over
                        pending_read        = !rd_packet_over;
                    end
                    rd_pending_rslv     = 0;
                end

                ref_model.tick();
            end
        endtask : run_phase
    endclass : fifo_norm_rm
endpackage : hs_fifo_sfifo_uvm_rm_pkg