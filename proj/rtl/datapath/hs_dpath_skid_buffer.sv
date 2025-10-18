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
// FILE NAME: hs_dpath_skid_buffer.sv
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
// PURPOSE: Skid buffer with standard handshake interface
//   Used to ease the timing of a streaming data interface by inserting
//   register stages on the data and/or control signals
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE          DESCRIPTION                 DEFAULT VALUE
// DATA_TYPE           type           Data type to interchange    logic
// FULL_THROUGHPUT     bool_e         High throughput mode/       BOOL_TRUE
//                                    Low resources cost mode
// CTRL_PIPE           bool_e         Ensures that there is no    BOOL_TRUE
//                                    combinatorial path on ctrl.
//                                    path between I/O
// DATA_PIPE           bool_e         Ensures that there is no    BOOL_TRUE
//                                    combinatorial path on data
//                                    path between I/O
// STROBE_UNIT         1-$bits(type)  Strobe unit width of packed 8
//                                    data
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// Skid buffer with standard handshake interface
module hs_dpath_skid_buffer
import hs_ifr_misc_typedefs_pkg::*;
#(
    parameter type   DATA_TYPE       = logic,
    parameter bool_e FULL_THROUGHPUT = BOOL_TRUE,
    parameter bool_e CTRL_PIPE       = BOOL_TRUE,
    parameter bool_e DATA_PIPE       = BOOL_TRUE,
    parameter int    STROBE_UNIT     = 8,
    `LP_MODULE int   STROBE_WIDTH    = $bits(DATA_TYPE) / STROBE_UNIT
)
(
    // Clock & reset
    input  logic                          clk,
    input  logic                          aresetn,

    // Data input side
    input  DATA_TYPE                      in_data,
    input  logic                          in_valid,
    input  logic                          in_last,
    output logic                          in_ready,
    input  logic     [STROBE_WIDTH - 1:0] in_strobe,

    // Data output side
    output DATA_TYPE                      out_data,
    output logic                          out_valid,
    output logic                          out_last,
    input  logic                          out_ready,
    output logic     [STROBE_WIDTH - 1:0] out_strobe
);

typedef logic [STROBE_WIDTH - 1:0] strobe_t;

typedef enum logic[1:0] {
    STATE_WAIT_FOR_IVALID,
    STATE_FULL_HANDSHAKE,
    STATE_WAIT_FOR_OREADY
} state_e;

logic out_valid_int;
logic in_ready_int;

assign out_valid = out_valid_int;
assign in_ready  = in_ready_int;

`GENERATE_START
if ((FULL_THROUGHPUT == BOOL_TRUE) && (CTRL_PIPE == BOOL_TRUE) && (DATA_PIPE == BOOL_TRUE)) begin : fth_cp_dp
    // This mode is a full buffered mode.

    // It makes sure that all output signals (data as well as control signals) are driven by
    // a register.  It does so while sustaining full throughput. It has the best timing
    // characteristics but also the largest logic footprint.

    state_e   state;

    DATA_TYPE in_data_buf;
    logic     in_last_buf;
    strobe_t  in_strobe_buf;

    always_ff @(posedge clk) begin : in_buffer
        if (in_valid && in_ready) begin
            in_data_buf   <= in_data;
            in_last_buf   <= in_last;
            in_strobe_buf <= in_strobe;
        end
    end : in_buffer

    always_ff @(posedge clk, negedge aresetn) begin
        if (!aresetn) begin
            in_ready_int  <= '0;

            out_valid_int <= '0;
            out_last      <= '0;

            state         <= STATE_WAIT_FOR_IVALID;
        end
        else begin
            case (state)
                STATE_WAIT_FOR_IVALID: begin
                    in_ready_int <= '1;

                    if (in_valid && in_ready_int) begin
                        out_valid_int <= '1;
                        out_last      <= in_last;
                        out_data      <= in_data;
                        out_strobe    <= in_strobe;

                        state         <= STATE_FULL_HANDSHAKE;
                    end
                end
                STATE_FULL_HANDSHAKE: begin
                    if (in_valid && out_ready) begin
                        // Both valid and ready are high, move data
                        out_last      <= in_last;
                        out_data      <= in_data;
                        out_strobe    <= in_strobe;
                    end
                    else if (out_ready) begin
                        // Only output transaction happens, disable output next cycle
                        out_valid_int <= '0;
                    end
                    else if (in_valid) begin
                        // Only input transaction happens, un-allow next input cycle
                        // And go to the wait for ready state
                        in_ready_int  <= '0;

                        state         <= STATE_WAIT_FOR_OREADY;
                    end
                end
                STATE_WAIT_FOR_OREADY: begin
                    if (out_ready) begin
                        // The output goes ready, copy buffered data to it
                        in_ready_int  <= '1;

                        out_last      <= in_last_buf;
                        out_data      <= in_data_buf;
                        out_strobe    <= in_strobe_buf;

                        // Go back to the handshake stage
                        state         <= STATE_FULL_HANDSHAKE;
                    end
                end
            endcase
        end
    end
end : fth_cp_dp
else if ((FULL_THROUGHPUT == BOOL_TRUE) && (CTRL_PIPE == BOOL_FALSE) && (DATA_PIPE == BOOL_TRUE)) begin : fth_dp
    // Full throughput, data pipeline enabled
    // In this mode, the data and control signals are driven by registers, except for in_ready
    // which will have an increased critical path. It still maintains full throughput,
    // and has a much smaller footprint than the full buffer.

    // It is suitable in situations where there is a complex net driving the data, which needs to
    // be pipelined in order to achieve timing closure, but the timing of the control signals is
    // not critical

    assign in_ready_int = out_ready || !out_valid_int;

    always_ff @(posedge clk, negedge aresetn) begin : fth_dp_ctrl_path
        if (!aresetn) begin
            out_valid_int <= '0;
            out_last      <= '0;
        end
        else begin
            if (in_ready_int) begin
                out_valid_int <= in_valid;
                out_last      <= in_last;
            end
        end
    end : fth_dp_ctrl_path


    always_ff @(posedge clk) begin : fth_dp_data_path
        if (in_ready_int) begin
            out_data   <= in_data;
            out_strobe <= in_strobe;
        end
    end : fth_dp_data_path
end : fth_dp
else if ((FULL_THROUGHPUT == BOOL_FALSE) && (CTRL_PIPE == BOOL_TRUE) && (DATA_PIPE == BOOL_TRUE)) begin : lac_cp_dp
    // All signals are driven by registers, which results in the best timing but also the lowest
    // throughput. This mode will be able to maintain a one third throughput.

    always_ff @(posedge clk, negedge aresetn) begin : lac_cp_dp_ctrl_path
        if (!aresetn) begin
            in_ready_int  <= '0;
            out_valid_int <= '0;
            out_last      <= '0;
        end
        else begin
            in_ready_int  <= out_ready && out_valid_int;
            out_valid_int <= in_valid && !(out_valid_int && out_ready) && !in_ready_int;
            out_last      <= in_last;
        end
    end : lac_cp_dp_ctrl_path


    always_ff @(posedge clk) begin : lac_cp_dp_data_path
        out_data   <= in_data;
        out_strobe <= in_strobe;
    end : lac_cp_dp_data_path

end : lac_cp_dp
else if ((FULL_THROUGHPUT == BOOL_FALSE) && (CTRL_PIPE == BOOL_FALSE) && (DATA_PIPE == BOOL_TRUE)) begin : lac_dp
    // All signals are driven by registers, except input_ready which will have an increased
    // critical path. This mode will be able to maintain a one half throughput.

    assign in_ready_int = out_ready && out_valid_int;


    always_ff @(posedge clk, negedge aresetn) begin : lac_dp_ctrl_path
        if (!aresetn) begin
            out_valid_int <= '0;
            out_last      <= '0;
        end
        else begin
            out_valid_int <= in_valid && !(out_valid_int && out_ready);
            out_last      <= in_last;
        end
    end : lac_dp_ctrl_path


    always_ff @(posedge clk) begin : lac_dp_data_path
        out_data   <= in_data;
        out_strobe <= in_strobe;
    end : lac_dp_data_path

end : lac_dp
else if ((CTRL_PIPE == BOOL_TRUE) && (DATA_PIPE == BOOL_FALSE)) begin : no_dp
    if (FULL_THROUGHPUT == BOOL_TRUE) begin : en_fth_no_dp
        initial $fatal(1, "Enable full throughput when only pipelining control signals is not allowed.");
    end : en_fth_no_dp

    state_e   state;

    always_comb begin : pass_th_no_dp
        out_data      = in_data;
        out_strobe    = in_strobe;
        out_last      = in_last;
    end : pass_th_no_dp

    always_ff @(posedge clk, negedge aresetn) begin : no_dp_ctrl_path
        if (!aresetn) begin
            in_ready_int  <= '0;
            out_valid_int <= '0;

            state         <= STATE_WAIT_FOR_IVALID;
        end
        else begin
            case (state)
                STATE_WAIT_FOR_IVALID: begin
                    in_ready_int <= '0;

                    // Proceed to output the input data, but only if we are not waiting for a pop
                    // of the previous input
                    if (in_valid && !in_ready_int) begin
                        out_valid_int <= '1;
                        state         <= STATE_WAIT_FOR_OREADY;
                    end
                end
                STATE_WAIT_FOR_OREADY: begin
                    if (out_ready) begin
                        in_ready_int  <= '1;
                        out_valid_int <= '0;
                        state         <= STATE_WAIT_FOR_IVALID;
                    end
                end
                default: state   <= STATE_WAIT_FOR_IVALID;
            endcase
        end
    end : no_dp_ctrl_path
end : no_dp
else if ((CTRL_PIPE == BOOL_FALSE) && (DATA_PIPE == BOOL_FALSE)) begin : pass_through
    always_comb begin : pass_th
        in_ready_int  = out_ready;
        out_valid_int = in_valid;
        out_data      = in_data;
        out_strobe    = in_strobe;
        out_last      = in_last;
    end : pass_th
end : pass_through
else begin : invalid_param
    initial $fatal(1, "Invalid parameter");
end : invalid_param
`GENERATE_END

endmodule : hs_dpath_skid_buffer