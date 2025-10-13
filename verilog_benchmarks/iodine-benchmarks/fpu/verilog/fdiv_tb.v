// fdiv_tb.v
// Testbench adapted for the division-only FPU module.
`timescale 1ns/1ps

module fdiv_tb (
  input clk,
  input clear_done   // pulse to clear sticky done
);

  // ============================================
  // Fixed Constants
  localparam [1:0] RMODE_FIXED = 2'd0; // Rounding mode: nearest-even
  localparam [2:0] FPU_OP_DIV  = 3'd3; // FPU operation: division

  // ============================================
  // Operand selectors: symbolic at init, then self-holding
  (* keep, public = "true" *) reg [1:0] opa_sel_q;
  (* keep, public = "true" *) reg [1:0] opb_sel_q;

  // Mirrors for observability
  (* keep, public = "true" *) reg [2:0] fpu_op_q;
  (* keep, public = "true" *) reg [1:0] rmode_q;

  always @(posedge clk) begin
    opa_sel_q <= opa_sel_q;
    opb_sel_q <= opb_sel_q;
    fpu_op_q  <= fpu_op_q;
    rmode_q   <= rmode_q;
  end

  // ============================================
  // LUT: 4 entries for operands
  function [31:0] fp_lut(input [1:0] s);
    case (s)
      2'd0: fp_lut = 32'h0000_0000; // +0.0
      2'd1: fp_lut = 32'h3f80_0000; // +1.0
      2'd2: fp_lut = 32'h4000_0000; // +2.0
      default: fp_lut = 32'h7f80_0000; // +Inf
    endcase
  endfunction

  wire [31:0] opa_w = fp_lut(opa_sel_q);
  wire [31:0] opb_w = fp_lut(opb_sel_q);

  // ============================================
  // DUT (Device Under Test)
  wire [31:0] out_w;
  wire inf_w, snan_w, qnan_w, ine_w, overflow_w, underflow_w, zero_w, div_by_zero_w;

  // Instantiating the division-only FPU
  fpu dut (
    .clk(clk),
    .rmode(RMODE_FIXED),
    .fpu_op(FPU_OP_DIV), // Operation is now hardwired to division
    .opa(opa_w),
    .opb(opb_w),
    .out(out_w),
    .inf(inf_w), .snan(snan_w), .qnan(qnan_w),
    .ine(ine_w),
    .overflow(overflow_w), .underflow(underflow_w),
    .zero(zero_w),
    .div_by_zero(div_by_zero_w)
  );

  // ============================================
  // Registered observable outputs
  (* keep, public = "true" *) reg [31:0] opa_q, opb_q, out_q;
  (* keep, public = "true" *) reg        inf_q, snan_q, qnan_q;
  (* keep, public = "true" *) reg        ine_q, overflow_q, underflow_q;
  (* keep, public = "true" *) reg        zero_q, div_by_zero_q;
  (* keep, public = "true" *) reg        done;

  // 'done' becomes true when any output changes
  wire changed =
        (out_q         != out_w)      ||
        (inf_q         != inf_w)      ||
        (snan_q        != snan_w)     ||
        (qnan_q        != qnan_w)     ||
        (ine_q         != ine_w)      ||
        (overflow_q    != overflow_w) ||
        (underflow_q   != underflow_w)||
        (zero_q        != zero_w)     ||
        (div_by_zero_q != div_by_zero_w);

  // ============================================
  // Initial state: outputs and flags cleared
  initial begin
    opa_q         = 32'h0000_0000;
    opb_q         = 32'h0000_0000;
    out_q         = 32'h0000_0000;
    inf_q         = 1'b0;
    snan_q        = 1'b0;
    qnan_q        = 1'b0;
    ine_q         = 1'b0;
    overflow_q    = 1'b0;
    underflow_q   = 1'b0;
    zero_q        = 1'b0;
    div_by_zero_q = 1'b0;
    done          = 1'b0;

    // Set mirrors to reflect the fixed operation
    fpu_op_q      = FPU_OP_DIV;
    rmode_q       = RMODE_FIXED;
  end

  // ============================================
  // Sequential update: capture all DUT outputs
  always @(posedge clk) begin
    opa_q <= opa_w;
    opb_q <= opb_w;

    out_q         <= out_w;
    inf_q         <= inf_w;
    snan_q        <= snan_w;
    qnan_q        <= qnan_w;
    ine_q         <= ine_w;
    overflow_q    <= overflow_w;
    underflow_q   <= underflow_w;
    zero_q        <= zero_w;
    div_by_zero_q <= div_by_zero_w;

    if (clear_done)
      done <= 1'b0;
    else
      done <= done | changed;
  end

endmodule