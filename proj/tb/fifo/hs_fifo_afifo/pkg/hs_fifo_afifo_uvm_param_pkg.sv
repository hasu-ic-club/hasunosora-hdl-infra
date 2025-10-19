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
// FILE NAME: hs_fifo_afifo_uvm_param_pkg.sv
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
// PURPOSE: Package of parameter definitions for UVM framework of hs_fifo_afifo
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// N/A
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE

// Package of parameter definitions for UVM framework of hs_fifo_afifo
package hs_fifo_afifo_uvm_param_pkg;
    import hs_ifr_misc_typedefs_pkg::*;

    // Default parameters
    `ifndef UVM_PARAM_DATA_WIDTH
    `define UVM_PARAM_DATA_WIDTH       16
    `endif

    `ifndef UVM_PARAM_FIFO_DEPTH
    `define UVM_PARAM_FIFO_DEPTH       32
    `endif

    `ifndef UVM_PARAM_ALMOST_FULL_LVL
    `define UVM_PARAM_ALMOST_FULL_LVL  `UVM_PARAM_FIFO_DEPTH
    `endif

    `ifndef UVM_PARAM_ALMOST_EMPTY_LVL
    `define UVM_PARAM_ALMOST_EMPTY_LVL 0
    `endif

    `ifndef UVM_PARAM_EN_LAST_SIGNAL
    `define UVM_PARAM_EN_LAST_SIGNAL   0
    `endif

    `ifndef UVM_PARAM_EN_PACKET_MODE
    `define UVM_PARAM_EN_PACKET_MODE   0
    `endif

    `ifndef UVM_PARAM_EN_DROP_PACKET
    `define UVM_PARAM_EN_DROP_PACKET   0
    `endif
    

    `ifndef UVM_PARAM_EN_OUTPUT_REG
    `define UVM_PARAM_EN_OUTPUT_REG    0
    `endif
    
    localparam type   DATA_TYPE        = logic[`UVM_PARAM_DATA_WIDTH - 1:0];
    localparam int    FIFO_DEPTH       = `UVM_PARAM_FIFO_DEPTH;
    localparam int    ALMOST_FULL_LVL  = `UVM_PARAM_ALMOST_FULL_LVL;
    localparam int    ALMOST_EMPTY_LVL = `UVM_PARAM_ALMOST_EMPTY_LVL;
    localparam bool_e EN_LAST_SIGNAL   = bit_to_bool(`UVM_PARAM_EN_LAST_SIGNAL);
    localparam bool_e EN_PACKET_MODE   = bit_to_bool(`UVM_PARAM_EN_PACKET_MODE);
    localparam bool_e EN_DROP_PACKET   = bit_to_bool(`UVM_PARAM_EN_DROP_PACKET);
    localparam bool_e EN_OUTPUT_REG    = bit_to_bool(`UVM_PARAM_EN_OUTPUT_REG );
endpackage  : hs_fifo_afifo_uvm_param_pkg