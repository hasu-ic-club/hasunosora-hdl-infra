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
// FILE NAME: hs_math_basic_pkg.sv
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
// PURPOSE: Basic math functions package
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// N/A
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// Basic math functions package
package hs_math_basic_pkg;
    // ReLU
    function automatic int relu(int value);
        return (value < 0) ? 0 : value;
    endfunction : relu

    // Clamp
    function automatic int clamp(int value, int min, int max);
        if (value < min) return min;
        else if (value > max) return max;
        else return value;
    endfunction : clamp

    // Map
    function automatic int map(int value, int in_min, int in_max, int out_min, int out_max);
        return (value - in_min) * (out_max - out_min) / (in_max - in_min) + out_min;
    endfunction : map

    // Get greatest common divisor (GCD)
    function automatic int gcd(int arg_x, int arg_y);
        if (arg_y == 0) return arg_x;
        else return gcd(arg_y, arg_x % arg_y);
    endfunction

    // Get least common multiple (LCM)
    function automatic int lcm(int arg_x, int arg_y);
        return arg_x * arg_y / gcd(arg_x, arg_y);
    endfunction : lcm

    // Get ceil(dividend / divisor)
    function automatic int ceil_div(int dividend, int divisor);
        automatic int quotient = dividend / divisor;
        automatic int revised  = quotient * divisor;
        return (revised != dividend) ? quotient + 1 : quotient;
    endfunction
    
    // Return 1 if the value is a power of 2
    function automatic bit is_pow2(int value);
        return ((value) & (value - 1)) == 0; 
    endfunction : is_pow2
    
    // Return the minimum power of 2 number greater than value 
    function automatic int ceil_to_nxt_pow2(int value);
        automatic int bits = $clog2(value); 
        
        if (is_pow2(value)) return value;
        
        return 2 ** bits;
    endfunction : ceil_to_nxt_pow2


    // Return the hamming distance of 2 number (<64-bit)
    function automatic int hamming_dist(longint unsigned arg_a, longint unsigned arg_b);
        longint xor_result = arg_a ^ arg_b;
        return $countones(xor_result);
    endfunction : hamming_dist
endpackage : hs_math_basic_pkg