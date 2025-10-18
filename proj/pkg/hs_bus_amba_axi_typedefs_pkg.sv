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
// FILE NAME: hs_bus_amba_axi_typedefs_pkg.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a0
// VERSION DESCRIPTION: First Edition
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/10/16    First Edition
//-----------------------------------------------------------------------
// PURPOSE:
//  Package for type definitions of ARM AMBA AXI interfaces
//-----------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME    RANGE         DESCRIPTION            DEFAULT VALUE
// N/A
//-FHDR------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// Package for type definitions of ARM AMBA AXI interfaces
package hs_bus_amba_axi_typedefs_pkg;
    function automatic logic [2:0] get_axsize(input int data_width);
        return $clog2(data_width / 8);
    endfunction : get_axsize

    typedef enum logic [1:0]
    {
        AxBURST_FIXED    = 2'b00,
        AxBURST_INCR     = 2'b01,
        AxBURST_WRAP     = 2'b10,
        AxBURST_RESERVED = 2'b11
    } axburst_e;

    typedef struct packed
    {
        logic allocate;
        logic other_allocate;
        logic modifiable;
        logic bufferable;
    } awcache_s;

    typedef struct packed
    {
        logic other_allocate;
        logic allocate;
        logic modifiable;
        logic bufferable;
    } arcache_s;

    typedef struct packed
    {
        logic data_instruction;
        logic secure;
        logic privileged;
    } axprot_s;

    typedef enum logic [1:0]
    {
        AxDOMAIN_NON_SHAREABLE = 2'b00,
        AxDOMAIN_SHAREABLE_1   = 2'b01,
        AxDOMAIN_SHAREABLE_2   = 2'b10,
        AxDOMAIN_SYSTEM        = 2'b11
    } axdomain_e;

    typedef enum logic [1:0]
    {
        AXMMUFLOW_STALL   = 2'b00,
        AXMMUFLOW_ATST    = 2'b01,
        AXMMUFLOW_NOSTALL = 2'b10,
        AXMMUFLOW_PRI     = 2'b11
    } axmmuflow_e;

    typedef enum logic [2:0]
    {
        AWATOP_MSB_NON_ATOMIC  = 3'b000,
        AWATOP_MSB_ATOM_STR_LE = 3'b010,
        AWATOP_MSB_ATOM_STR_BE = 3'b011,
        AWATOP_MSB_ATOM_LDR_LE = 3'b100,
        AWATOP_MSB_ATOM_LDR_BE = 3'b101,
        AWATOP_MSB_ATOM_SWCMP  = 3'b110
    } awatop_msb_e;

    typedef enum logic [2:0]
    {
        AWATOP_LSB_ADD_SWAP = 3'b000,
        AWATOP_LSB_CLR_CMP  = 3'b001,
        AWATOP_LSB_EOR      = 3'b010,
        AWATOP_LSB_SET      = 3'b011,
        AWATOP_LSB_SMAX     = 3'b100,
        AWATOP_LSB_SMIN     = 3'b101,
        AWATOP_LSB_UMAX     = 3'b110,
        AWATOP_LSB_UMIN     = 3'b111
    } awatop_lsb_e;

    typedef struct packed
    {
        awatop_msb_e msb;
        awatop_lsb_e lsb;
    } awatop_s;

    typedef enum logic[1:0]
    {
        AWTAGOP_INVLAID  = 2'b00,
        AWTAGOP_TRANSFER = 2'b01,
        AWTAGOP_UPDATE   = 2'b10,
        AWTAGOP_MATCH    = 2'b11
    } awtagop_e;

    typedef enum logic[1:0]
    {
        ARTAGOP_INVLAID  = 2'b00,
        ARTAGOP_TRANSFER = 2'b01,
        ARTAGOP_RESERVED = 2'b10,
        ARTAGOP_FETCH    = 2'b11
    } artagop_e;

    typedef enum logic [2:0]
    {
        BRESP_3B_OKAY        = 3'b000,
        BRESP_3B_EXOKAY      = 3'b001,
        BRESP_3B_SLVERR      = 3'b010,
        BRESP_3B_DECERR      = 3'b011,
        BRESP_3B_DEFER       = 3'b100,
        BRESP_3B_TRANSFAULT  = 3'b101,
        BRESP_3B_RESERVED    = 3'b110,
        BRESP_3B_UNSUPPORTED = 3'b111
    } bresp_3b_e;

    typedef enum logic [1:0]
    {
        BRESP_2B_OKAY        = 2'b00,
        BRESP_2B_EXOKAY      = 2'b01,
        BRESP_2B_SLVERR      = 2'b10,
        BRESP_2B_DECERR      = 2'b11
    } bresp_2b_e;

    typedef enum logic [2:0]
    {
        RRESP_3B_OKAY        = 3'b000,
        RRESP_3B_EXOKAY      = 3'b001,
        RRESP_3B_SLVERR      = 3'b010,
        RRESP_3B_DECERR      = 3'b011,
        RRESP_3B_PREFETCHED  = 3'b100,
        RRESP_3B_TRANSFAULT  = 3'b101,
        RRESP_3B_OKAYDIRTY   = 3'b110,
        RRESP_3B_RESERVED    = 3'b111
    } rresp_3b_e;

    typedef enum logic [1:0]
    {
        RRESP_2B_OKAY        = 2'b00,
        RRESP_2B_EXOKAY      = 2'b01,
        RRESP_2B_SLVERR      = 2'b10,
        RRESP_2B_DECERR      = 2'b11
    } rresp_2b_e;

    typedef enum logic [1:0]
    {
        xBUSY_NOT_BUSY     = 2'b00,
        xBUSY_OPTIMAL_BUSY = 2'b01,
        xBUSY_QUITE_BUSY   = 2'b10,
        xBUSY_VERY_BUSY    = 2'b11
    } xbusy_e;
endpackage : hs_bus_amba_axi_typedefs_pkg

