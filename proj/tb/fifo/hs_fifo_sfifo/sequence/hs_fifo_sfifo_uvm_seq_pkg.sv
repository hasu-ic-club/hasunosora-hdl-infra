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
// FILE NAME: hs_fifo_sfifo_uvm_seq_pkg.sv
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
// PURPOSE: Package of sequence definition for UVM framework of hs_fifo_sfifo
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// N/A
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE

// Package of sequence definition for UVM framework of hs_fifo_sfifo
package hs_fifo_sfifo_uvm_seq_pkg;
    import uvm_pkg::*;
    import hs_ifr_misc_typedefs_pkg::*;
    import hs_fifo_sfifo_uvm_param_pkg::*;
    import hs_fifo_sfifo_uvm_seqitem_pkg::*;

    `include "uvm_macros.svh"

    class fifo_write_base_seq extends uvm_sequence#(fifo_write_tr);

        int n_beats;

        function new(string name="wr_base_seq");
            super.new(name);
        endfunction : new
    endclass : fifo_write_base_seq


    class fifo_read_base_seq extends uvm_sequence#(fifo_read_tr);

        int n_beats;

        function new(string name="rd_base_seq");
            super.new(name);
        endfunction : new
    endclass : fifo_read_base_seq

    class fifo_burst_write_seq extends fifo_write_base_seq;
        `uvm_object_param_utils(fifo_burst_write_seq)

        function new(string name="wr_burst_seq");
            super.new(name);
        endfunction : new

        virtual task body();
            fifo_write_tr tr;

            for (int tr_id = 0; tr_id < n_beats; tr_id++) begin
                tr = new("tr");

                start_item(tr);
                assert (tr.randomize() with { stall_cycle dist {0 := 90, [1:5] := 10}; })
                else `uvm_error(this.get_type_name(), "Randomize failed for FIFO write transaction");

                `uvm_info(this.get_type_name(), $sformatf("Starting to write transaction %0d, stall = %0d, data = %h", tr_id, tr.stall_cycle, tr.data), UVM_HIGH);

                finish_item(tr);
            end
        endtask : body
    endclass

    class fifo_burst_read_seq extends fifo_read_base_seq;

        `uvm_object_param_utils(fifo_burst_read_seq)

        function new(string name="rd_burst_seq");
            super.new(name);
        endfunction : new

        virtual task body();
            fifo_read_tr tr;

            for (int tr_id = 0; tr_id < n_beats; tr_id++) begin
                tr = new("tr");

                start_item(tr);
                assert (tr.randomize() with { stall_cycle dist {0 := 80, [1:5] := 20}; })
                else `uvm_error(this.get_type_name(), "Randomize failed for FIFO read transaction");

                `uvm_info(this.get_type_name(), $sformatf("Starting to read transaction %0d, stall = %0d", tr_id, tr.stall_cycle), UVM_HIGH);

                finish_item(tr);
            end
        endtask : body
    endclass : fifo_burst_read_seq

    class fifo_package_write_seq extends fifo_write_base_seq;
        `uvm_object_param_utils(fifo_package_write_seq)

        rand int packet_len;
        rand int where_to_drop;

        constraint const_packet_len {
            packet_len dist {0 := 80, [1:FIFO_DEPTH] := 20};
            where_to_drop dist { -1 := 95, [0:packet_len - 1] := 5};
        }

        function new(string name="wr_package_seq");
            super.new(name);
        endfunction : new

        virtual task body();
            fifo_write_tr tr;

            for (int beat = 0; beat < n_beats; beat++) begin
                assert (this.randomize())
                else `uvm_error(this.get_type_name(), "Randomize failed for FIFO package write sequence");

                if (packet_len == 0) begin
                    tr = fifo_write_tr::type_id::create("tr");

                    `uvm_do_with(tr, {stall_cycle == 5;});

                    continue;
                end

                `uvm_info(this.get_type_name(), $sformatf("Starting to write package %0d, length = %0d", beat, packet_len), UVM_HIGH);

                for (int tr_id = 0; tr_id < packet_len; tr_id++) begin
                    automatic bit last;
                    automatic bit drop;

                    tr   = fifo_write_tr::type_id::create("tr");

                    last = (tr_id == packet_len - 1);
                    drop = (where_to_drop == tr_id);

                    `uvm_do_with(tr, {last == last; stall_cycle == 0; drop == drop;});
                end
            end
        endtask : body
    endclass : fifo_package_write_seq

    class fifo_package_read_req extends fifo_read_base_seq;
        `uvm_object_param_utils(fifo_package_read_req)

        rand bit peek;

        constraint const_peek {
            peek dist {0 := 70, 1 := 30};
        }

        function new(string name="rd_package_req");
            super.new(name);
        endfunction : new

        virtual task body();
            fifo_read_tr tr;

            for (int beat = 0; beat < n_beats; beat++) begin
                assert (this.randomize())
                else `uvm_error(this.get_type_name(), "Randomize failed for FIFO package write sequence");

                tr = fifo_read_tr::type_id::create("tr");

                `uvm_do_with(tr, {stall_cycle inside {[0:10]}; peek == peek;});  
            end
        endtask : body
    endclass : fifo_package_read_req
endpackage : hs_fifo_sfifo_uvm_seq_pkg