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
# FILE NAME: hs_cdc_syncer.xdc
# AUTHOR:    Onodera Tsusaki
# EMAIL:     apertureelectronic@outlook.com
#-------------------------------------------------------------------------
# RELEASE VERSION: 0.1a0
# VERSION DESCRIPTION: First Edition
#-------------------------------------------------------------------------
# RELEASES:
# VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
# 0.1a0      O. Tsusaki    2025/9/25     First Edition
#-------------------------------------------------------------------------
# PURPOSE: Xilinx constraint for multi-stage asynchronous synchronizer (1-bit)
#
#-FHDR--------------------------------------------------------------------

# Get synchronizer flip-flops
set sync_ffs [get_cells -quiet -hier -regexp {^.*sync_ff(_reg)?\[[0-9]+\]$}]

# Asynchronous register
set_property ASYNC_REG TRUE $sync_ffs
set_property SHREG_EXTRACT NO $sync_ffs

# Set the false path
set first_d_pin [get_pins -quiet -filter {REF_PIN_NAME == "D"} -of [get_cells -hier -regexp {^.*sync_ff(_reg)?\[0\]$}]]
set_false_path -to $first_d_pin

