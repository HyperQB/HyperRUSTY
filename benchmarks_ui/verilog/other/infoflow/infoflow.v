`timescale 1ns / 1ps
`default_nettype none
`define assert(expression) \
        if (!(expression)) begin \
            $display("ASSERTION FAILED"); \
            $finish; \
        end   

module main (
    input  wire       clk,          // system clock
    input  wire       rst,          // active-high sync reset
    input  wire       high_choice,  // external nondet choice
    output reg        high,
    output reg        low,
    output reg  [2:0] PC,
    output reg        halt
);

  // next‐state signals
  reg        nxt_high, nxt_low, nxt_halt;
  reg [2:0]  nxt_PC;

  // combinational next‐state logic
  always @* begin
    // defaults: hold current values
    nxt_high = high;
    nxt_low  = low;
    nxt_PC   = PC;
    nxt_halt = halt;

    case (PC)
      3'd1: begin
        nxt_high = high_choice;  // pulled‐out nondeterminism
        nxt_PC   = 3'd2;
      end

      3'd2: begin
        nxt_low = 1'b0;
        nxt_PC  = 3'd3;
      end

      3'd3: begin
        if (high)
          nxt_PC = 3'd4;
        else
          nxt_PC = 3'd5;
      end

      3'd4: begin
        nxt_low = 1'b1;
        nxt_PC  = 3'd5;
      end

      3'd5: begin
        nxt_halt = 1'b1;
        nxt_PC   = 3'd5;
      end

      default: begin
        // stay in current state
      end
    endcase
  end

  // sequential state updates with synchronous reset
  always @(posedge clk) begin
    begin
      high  <= nxt_high;
      low   <= nxt_low;
      halt  <= nxt_halt;
      PC    <= nxt_PC;
    end
  end

endmodule
