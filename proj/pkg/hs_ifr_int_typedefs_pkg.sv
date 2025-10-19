//+FHDR------------------------------------------------------------------
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
//-----------------------------------------------------------------------
// FILE NAME: hs_ifr_int_typedefs_pkg.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-----------------------------------------------------------------------
// RELEASE VERSION:     0.1a0
// VERSION DESCRIPTION: Initial version
//-----------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/09       Initial version
//-----------------------------------------------------------------------
// PURPOSE:
//  Package for integer type definitions
//-----------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME    RANGE         DESCRIPTION            DEFAULT VALUE
//-----------------------------------------------------------------------
// N/A
//-FHDR------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE

// Package for integer type definitions
package hs_ifr_int_typedefs_pkg;
    // Unsigned integers
    typedef logic [7:0]  lg_uint8_t;
    typedef logic [15:0] lg_uint16_t;
    typedef logic [31:0] lg_uint32_t;
    typedef logic [63:0] lg_uint64_t;

    // Signed integers
    typedef logic signed [7:0]  lg_int8_t;
    typedef logic signed [15:0] lg_int16_t;
    typedef logic signed [31:0] lg_int32_t;
    typedef logic signed [63:0] lg_int64_t;

    // Unsigned integers (bit)
    typedef bit [7:0]  uint8_t;
    typedef bit [15:0] uint16_t;
    typedef bit [31:0] uint32_t;
    typedef bit [63:0] uint64_t;

    // Signed integers (bit)
    typedef bit signed [7:0]  int8_t;
    typedef bit signed [15:0] int16_t;
    typedef bit signed [31:0] int32_t;
    typedef bit signed [63:0] int64_t;

    // Named integers
    typedef lg_uint8_t  lg_byte_t;
    typedef lg_uint16_t lg_halfword_t;
    typedef lg_uint32_t lg_word_t;
    typedef lg_int8_t   lg_sbyte_t;
    typedef lg_int16_t  lg_shalfword_t;
    typedef lg_int32_t  lg_sword_t;
endpackage : hs_ifr_int_typedefs_pkg
