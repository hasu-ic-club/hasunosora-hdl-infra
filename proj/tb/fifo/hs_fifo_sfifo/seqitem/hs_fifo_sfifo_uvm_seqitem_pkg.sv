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
// FILE NAME: hs_fifo_sfifo_uvm_seqitem.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a0
// VERSION DESCRIPTION: First Edition
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/9/14     First Edition
//-------------------------------------------------------------------------
// PURPOSE: Package of sequence item definition for UVM framework of hs_fifo_sfifo
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// N/A
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// Package of sequence item definition for UVM framework of hs_fifo_sfifo
package hs_fifo_sfifo_uvm_seqitem_pkg;
    import uvm_pkg::*;
    import hs_ifr_misc_typedefs_pkg::*;
    import hs_fifo_sfifo_uvm_param_pkg::*;

    `include "uvm_macros.svh"

    class fifo_write_tr extends uvm_sequence_item;
        rand DATA_TYPE    data;
        rand bit          last;
        rand int          stall_cycle;
        rand bit          drop;

        constraint constr_last
        {
            (EN_LAST_SIGNAL == BOOL_FALSE) -> last == '0;
        }

        constraint constr_drop
        {
            ((EN_PACKET_MODE == BOOL_FALSE) || (EN_DROP_PACKET == BOOL_FALSE)) -> drop == '0;
        }

        function new(string name = "wr_tr");
            super.new(name);
        endfunction : new

        `uvm_object_utils_begin(fifo_write_tr)
            `uvm_field_int (data,        UVM_DEFAULT)
            `uvm_field_int (last,        UVM_DEFAULT)
            `uvm_field_int (stall_cycle, UVM_DEFAULT)
            `uvm_field_int (drop,        UVM_DEFAULT)
        `uvm_object_utils_end
    endclass : fifo_write_tr

    class fifo_read_tr extends uvm_sequence_item;
        rand bit          peek;
        rand int          stall_cycle;

        constraint constr_peek
        {
            ((EN_PACKET_MODE == BOOL_FALSE) || (EN_PEEK_MODE == BOOL_FALSE)) -> peek == '0;
        }

        function new(string name = "rd_tr");
            super.new(name);
        endfunction : new

        `uvm_object_utils_begin(fifo_read_tr)
            `uvm_field_int (peek,        UVM_DEFAULT)
            `uvm_field_int (stall_cycle, UVM_DEFAULT)
        `uvm_object_utils_end
    endclass : fifo_read_tr

    class fifo_write_mon_tr extends uvm_sequence_item;

        DATA_TYPE    data;
        bit          last;
        bit          drop;
        int          level;
        bit          almost_full;

        function new(string name = "wr_mon_tr");
            super.new(name);
        endfunction : new

        `uvm_object_utils_begin(fifo_write_mon_tr)
            `uvm_field_int (data,        UVM_DEFAULT)
            `uvm_field_int (last,        UVM_DEFAULT)
            `uvm_field_int (drop,        UVM_DEFAULT)
            `uvm_field_int (level,       UVM_DEFAULT)
            `uvm_field_int (almost_full, UVM_DEFAULT)
        `uvm_object_utils_end
    endclass : fifo_write_mon_tr

    class fifo_read_mon_tr extends uvm_sequence_item;

        DATA_TYPE data;
        bit       last;
        bit       peek;
        int       level;
        bit       almost_empty;

        function new(string name = "rd_mon_tr");
            super.new(name);
        endfunction : new

        `uvm_object_utils_begin(fifo_read_mon_tr)
            `uvm_field_int (data,         UVM_DEFAULT)
            `uvm_field_int (last,         UVM_DEFAULT)
            `uvm_field_int (peek,         UVM_DEFAULT)
            `uvm_field_int (level,        UVM_DEFAULT)
            `uvm_field_int (almost_empty, UVM_DEFAULT)
        `uvm_object_utils_end
    endclass : fifo_read_mon_tr
endpackage : hs_fifo_sfifo_uvm_seqitem_pkg