#+FHDR--------------------------------------------------------------------
# Copyright (C) 2025 Hasunosora IC Design Club
# MIT License
# Permission is hereby granted, free of charge, to any person obtaining a 
# copy of this design and associated documentation files (the “Design”), 
# to deal in the Design without restriction, including without limitation 
# the rights to use, copy, modify, merge, publish, distribute, sublicense, 
# and/or sell copies of the Design, and to permit persons to whom the 
# Design is furnished to do so, subject to the following conditions:
# The above copyright notice and this permission notice shall be included 
# in all copies or substantial portions of the Design.
#
# THE DESIGN IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, 
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF 
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. 
# IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, 
# DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, 
# TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE 
# DESIGN OR THE USE OR OTHER DEALINGS IN THE DESIGN.
#-------------------------------------------------------------------------
# FILE NAME: hs_cdc_2phase.xdc
# AUTHOR:    Onodera Tsusaki
# EMAIL:     apertureelectronic@outlook.com
#-------------------------------------------------------------------------
# RELEASE VERSION: 0.1a2
# VERSION DESCRIPTION: First Edition
#-------------------------------------------------------------------------
# RELEASES:
# VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
# 0.1a0      O. Tsusaki    2025/9/25     First Edition
# 0.1a1      O. Tsusaki    2025/10/22    Remove -hier option from get_ports.
#                                        It's a mistake.
# 0.1a2      O. Tsusaki    2025/10/22    Replace -regexp with -filter in 
#                                        get_ports for more robust matching.
#-------------------------------------------------------------------------
# PURPOSE: Xilinx constraint for 2-phase clock domain cross for multi-bit data
#
#-FHDR--------------------------------------------------------------------

# Get the clock
set src_clk [get_clocks -quiet -of [get_ports -filter {NAME =~ *src_clk}]]
set dst_clk [get_clocks -quiet -of [get_ports -filter {NAME =~ *dst_clk}]]

# Get period of the clock
set src_clk_period [get_property PERIOD $src_clk]
set dst_clk_period [get_property PERIOD $dst_clk]

# Get the minimal period
set min_clk_period [expr {min(${src_clk_period}, ${dst_clk_period})}]

# Get the data-path flip-flops
set src_dffs [get_cells -quiet -hier -regexp {^.*src_reg(_reg)?(\[.*\])?\[[0-9]+\]$}]
set dst_dffs [get_cells -quiet -hier -regexp {^.*dst_reg(_reg)?(\[.*\])?\[[0-9]+\]$}]

# Set the max delay to impose a latency limit
set_max_delay -datapath_only -from ${src_dffs} -to ${dst_dffs} ${min_clk_period}
