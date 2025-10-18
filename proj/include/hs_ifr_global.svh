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
// FILE NAME: hs_ifr_global.svh
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a0
// VERSION DESCRIPTION: First Edition
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/9/9      First Edition
//-------------------------------------------------------------------------
// PURPOSE: Global settings header
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// N/A
//-FHDR--------------------------------------------------------------------

`ifndef HS_IFR_GLOBAL_SVH
`define HS_IFR_GLOBAL_SVH

// Enable to remove “`default_nettype none" at head of each RTL source file
// Some compilers do not recognize the "`default_nettype none" macro,
// or may give exceptions when set default nettype to none.
// NOTE: Designer should comment this switch while designing and linting for better
// code robustness. Only when a specific compiler encounters an error 
// for "default_nettype" should it consider turning on this switch for compilation.
// `define USE_DEFAULT_NETTYPE_WIRE
`ifdef USE_DEFAULT_NETTYPE_WIRE
`define DEFAULT_NETTYPE wire
`else // USE_DEFAULT_NETTYPE_WIRE
`define DEFAULT_NETTYPE none
`endif // USE_DEFAULT_NETTYPE_NONE

// These marco is for some compilers does not supported implicited generate 
// statements. If so, just de-comment the macro replacement.
`ifndef USE_EXPLICIT_GENERATE
    `ifndef GENERATE_START
    `define GENERATE_START // generate
    `endif

    `ifndef GENERATE_END
    `define GENERATE_END   // endgenerate
    `endif
`else  // !USE_EXPLICIT_GENERATE
    `ifndef GENERATE_START
    `define GENERATE_START generate
    `endif

    `ifndef GENERATE_END
    `define GENERATE_END   endgenerate
    `endif
`endif // USE_EXPLICIT_GENERATE

// This macro is for some compilers does not supported localparam on module 
// definition. If so, replace "localparam" to "parameter".
`ifndef DONT_USE_LOCALPARAM_ON_MODULE
    `ifndef LP_MODULE
    `define LP_MODULE localparam
    `endif
`else // !DONT_USE_LOCALPARAM_ON_MODULE
    `ifndef LP_MODULE
    `define LP_MODULE parameter
    `endif
`endif // DONT_USE_LOCALPARAM_ON_MODULE

// This macro is for the synthesis tools to optimize the register
// in asynchronous mode 
`ifndef ASYNC_REG_HINT
`define ASYNC_REG_HINT (* ASYNC_REG = "TRUE" *)
`endif


`endif // HS_IFR_GLOBAL_SVH