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
// FILE NAME: hs_ifr_misc_typedefs_pkg.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a0
// VERSION DESCRIPTION: First Edition
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/9/12     First Edition
//-------------------------------------------------------------------------
// PURPOSE: Package for misc type definitions
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// N/A
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// Package for misc type definitions
package hs_ifr_misc_typedefs_pkg;
    // Boolean type
    typedef enum bit {
        BOOL_FALSE = 0,
        BOOL_TRUE  = 1
    } bool_e;
    
    // 4-state Boolean type
    typedef enum logic {
        LG_BOOL_FALSE   = 1'b0,
        LG_BOOL_TRUE    = 1'b1,
        LG_BOOL_Z       = 1'bz
    } lg_bool_e;

    // Edge type
    typedef enum {
        EDGE_POSEDGE = 0,
        EDGE_NEGEDGE = 1,
        EDGE_BOTH    = 2
    } edge_e;
    
    // Level type
    typedef enum {
        LEVEL_LOW  = 0,
        LEVEL_HIGH = 1,
        LEVEL_BOTH = 2
    } level_e;
    
    function automatic bit bool_to_bit(bool_e val);
        return val == BOOL_TRUE ? 1 : 0;
    endfunction : bool_to_bit
    
    function automatic bool_e bit_to_bool(bit val);
        return val == 1 ? BOOL_TRUE : BOOL_FALSE;
    endfunction : bit_to_bool
endpackage : hs_ifr_misc_typedefs_pkg