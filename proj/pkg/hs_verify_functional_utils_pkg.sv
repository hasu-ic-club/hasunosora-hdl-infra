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
// FILE NAME: hs_verify_functional_utils_pkg.sv
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
// PURPOSE: Functional utils for verification
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// N/A
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE

// Functional utils for verification
package hs_verify_functional_utils_pkg;
    import hs_verify_lambda_pkg::*;
    
    // A class can implement the outer product
    // For each item in list A, take every item from list B in turn,
    // pair them together, and create a new object using a custom function.
    // This class will return the list of new objects
    class outer_product_c #(type DATA_TYPE_A = int,
            type DATA_TYPE_B = int,
            type DATA_TYPE_R = int
        );
        
        typedef DATA_TYPE_R rtn_type_queue[$];
        
        static function void apply(
                const ref DATA_TYPE_R list_r[$],
                const ref DATA_TYPE_A list_a[$], 
                const ref DATA_TYPE_B list_b[$],
                input hs_verify_lambda_pkg::lambda_2elem_c#(        DATA_TYPE_A, DATA_TYPE_B, DATA_TYPE_R
                ) merger);

            foreach (list_a[idx_a]) begin
                foreach (list_b[idx_b]) begin
                    list_r.push_back(merger.apply(list_a[idx_a], list_b[idx_b]));
                end
            end
        endfunction : apply
    endclass : outer_product_c
endpackage : hs_verify_functional_utils_pkg