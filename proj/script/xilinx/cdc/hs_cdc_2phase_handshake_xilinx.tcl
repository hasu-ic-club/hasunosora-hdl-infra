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
# FILE NAME: hs_cdc_2phase_handshake_xilinx.tcl
# AUTHOR:    Onodera Tsusaki
# EMAIL:     apertureelectronic@outlook.com
#-------------------------------------------------------------------------
# RELEASE VERSION: 0.1a0
# VERSION DESCRIPTION: First Edition
#-------------------------------------------------------------------------
# RELEASES:
# VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
# 0.1a0      O. Tsusaki    2025/9/26     First Edition
#-------------------------------------------------------------------------
# PURPOSE: Xilinx script for 2-phase clock domain cross for multi-bit 
#          data with handshake control
#
#-FHDR--------------------------------------------------------------------

set xdc_file [lindex [get_files *hs_cdc_2phase_handshake.xdc] 0]
if { $xdc_file ne "" } {
    set_property SCOPED_TO_REF hs_cdc_2phase_handshake [get_files $xdc_file]
}
