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
// FILE NAME: hs_fifo_sfifo_tb.sv
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
// PURPOSE: Testbench of Parameterized Synchronous FIFO
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// N/A
//-FHDR--------------------------------------------------------------------
`timescale 1ns/1ps

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

import uvm_pkg::*;
`include "uvm_macros.svh"


// Testbench of Parameterized Synchronous FIFO
module hs_fifo_sfifo_tb
import hs_fifo_sfifo_uvm_param_pkg::*;
import hs_ifr_misc_typedefs_pkg::*;
import hs_fifo_sfifo_uvm_test_pkg::*;
();

logic          clk;
logic          aresetn;

localparam int CLK_PERIOD = 5;
localparam int RST_PERIOD = 15;

hs_fifo_sfifo_duv_if duv_if
(
    .clk    (clk    ),
    .aresetn(aresetn)
);

// DUV
hs_fifo_sfifo #(
    .DATA_TYPE       (DATA_TYPE       ),
    .FIFO_DEPTH      (FIFO_DEPTH      ),
    .ALMOST_FULL_LVL (ALMOST_FULL_LVL ),
    .ALMOST_EMPTY_LVL(ALMOST_EMPTY_LVL),
    .EN_LAST_SIGNAL  (EN_LAST_SIGNAL  ),
    .EN_PACKET_MODE  (EN_PACKET_MODE  ),
    .EN_DROP_PACKET  (EN_DROP_PACKET  ),
    .EN_PEEK_MODE    (EN_PEEK_MODE    ),
    .EN_OUTPUT_REG   (EN_OUTPUT_REG   )
)
DUV (
    .clk          (clk                 ),
    .aresetn      (aresetn             ),
    .wvalid       (duv_if.wvalid       ),
    .wready       (duv_if.wready       ),
    .wdata        (duv_if.wdata        ),
    .wlast        (duv_if.wlast        ),
    .wdrop        (duv_if.wdrop        ),
    .walmost_full (duv_if.walmost_full ),
    .rready       (duv_if.rready       ),
    .rvalid       (duv_if.rvalid       ),
    .rdata        (duv_if.rdata        ),
    .rlast        (duv_if.rlast        ),
    .rpeek        (duv_if.rpeek        ),
    .ralmost_empty(duv_if.ralmost_empty),
    .level        (duv_if.level        )
);

// SVA
bind DUV hs_fifo_sfifo_sva #(
    .DATA_TYPE        (DATA_TYPE       ),
    .FIFO_DEPTH       (FIFO_DEPTH      ),
    .ALMOST_FULL_LVL  (ALMOST_FULL_LVL ),
    .ALMOST_EMPTY_LVL (ALMOST_EMPTY_LVL),
    .EN_LAST_SIGNAL   (EN_LAST_SIGNAL  ),
    .EN_PACKET_MODE   (EN_PACKET_MODE  ),
    .EN_DROP_PACKET   (EN_DROP_PACKET  ),
    .EN_PEEK_MODE     (EN_PEEK_MODE    ),
    .EN_OUTPUT_REG    (EN_OUTPUT_REG   )
) sva_inst (.*, .wdrop(wdrop));

// Test flow
initial begin
    automatic string test_name;
    automatic string param = $sformatf("Testing Parameter: almost_full_lvl = %02d, almost_empty_lvl = %02d, en_last_signal = %s, en_packet_mode = %s, en_drop_packet = %s, en_peek_mode = %s, en_output_reg = %s",
        ALMOST_FULL_LVL,
        ALMOST_EMPTY_LVL,
        bool_to_bit(EN_LAST_SIGNAL) ? "TRUE" : "FALSE",
        bool_to_bit(EN_PACKET_MODE) ? "TRUE" : "FALSE",
        bool_to_bit(EN_DROP_PACKET) ? "TRUE" : "FALSE",
        bool_to_bit(EN_PEEK_MODE  ) ? "TRUE" : "FALSE",
        bool_to_bit(EN_OUTPUT_REG ) ? "TRUE" : "FALSE"
    );

    `uvm_info("top", param, UVM_MEDIUM);
    uvm_config_db #(virtual hs_fifo_sfifo_duv_if)::set(uvm_root::get(), "", "vif", duv_if);
    uvm_config_db #(virtual hs_fifo_sfifo_duv_if.wr)::set(uvm_root::get(), "", "vif", duv_if.wr);
    uvm_config_db #(virtual hs_fifo_sfifo_duv_if.rd)::set(uvm_root::get(), "", "vif", duv_if.rd);

    run_test("fifo_burst_test");

    $finish;
end

// Clock generate
initial begin : clk_gen
    fork
        begin
            clk                   = 0;
            forever begin
                #(CLK_PERIOD / 2) clk = ~clk;
            end
        end
        begin
            aresetn               = 0;
            #(RST_PERIOD) aresetn = 1;
        end
    join
end : clk_gen

// Final report block
final begin
    automatic uvm_report_server srv = uvm_report_server::get_server();
    automatic int fatals =srv.get_severity_count(UVM_FATAL);

    if (fatals > 0) begin
        $fatal;
    end
end

endmodule : hs_fifo_sfifo_tb
