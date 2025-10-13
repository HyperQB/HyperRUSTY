/////////////////////////////////////////////////////////////////////
////                                                             ////
////  FPU (Division Only)                                        ////
////  Floating Point Unit (Single precision)                     ////
////                                                             ////
////  Author: Rudolf Usselmann                                   ////
////          rudi@asics.ws                                      ////
////  (Minimized for Division Only)                              ////
////                                                             ////
/////////////////////////////////////////////////////////////////////

`timescale 1ns / 100ps

`include "except.v"
`include "pre_norm_fmul.v"
`include "post_norm.v"

module fpu(clk, 
    rmode, fpu_op, opa, opb, 
    out, inf, snan, qnan, ine, overflow, underflow, zero, div_by_zero
    );
input       clk;
input   [1:0]   rmode;
input   [2:0]   fpu_op; // Kept for interface compatibility, but logic assumes division
input   [31:0]  opa, opb;
output  [31:0]  out;
output      inf, snan, qnan;
output      ine;
output      overflow, underflow;
output      zero;
output      div_by_zero;

parameter
    INF  = 31'h7f800000,
    QNAN = 31'h7fc00001;

// Local Wires
reg     zero;
reg [31:0]  opa_r, opb_r;
reg [31:0]  out;
reg     div_by_zero;
reg [7:0]   exp_r;
wire [30:0]  out_d;
wire        overflow_d, underflow_d;
reg     overflow, underflow;
reg     inf, snan, qnan;
reg     ine;
reg [1:0]   rmode_r1, rmode_r2, rmode_r3;
reg [2:0]   fpu_op_r1, fpu_op_r2, fpu_op_r3;
wire        div_inf;
wire        div_00;

////////////////////////////////////////////////////////////////////////
// Input Registers
always @(posedge clk) begin
    opa_r <= #1 opa;
    opb_r <= #1 opb;
    rmode_r1 <= #1 rmode;
    rmode_r2 <= #1 rmode_r1;
    rmode_r3 <= #1 rmode_r2;
    fpu_op_r1 <= #1 fpu_op;
    fpu_op_r2 <= #1 fpu_op_r1;
    fpu_op_r3 <= #1 fpu_op_r2;
end

////////////////////////////////////////////////////////////////////////
// Exceptions block
wire        inf_d, ind_d, qnan_d, snan_d, opa_nan, opb_nan;
wire        opa_00, opb_00;
wire        opa_inf, opb_inf;
wire        opa_dn, opb_dn;

except u0(  .clk(clk),
        .opa(opa_r), .opb(opb_r),
        .inf(inf_d), .ind(ind_d),
        .qnan(qnan_d), .snan(snan_d),
        .opa_nan(opa_nan), .opb_nan(opb_nan),
        .opa_00(opa_00), .opb_00(opb_00),
        .opa_inf(opa_inf), .opb_inf(opb_inf),
        .opa_dn(opa_dn), .opb_dn(opb_dn)
        );

////////////////////////////////////////////////////////////////////////
// Pre-Normalize block (for Mul/Div)
wire    nan_sign_d;
wire    [7:0]   exp_mul;
wire        sign_mul;
reg     sign_mul_r;
wire    [23:0]  fracta_mul, fractb_mul;
wire        sign_exe;
reg     sign_exe_r;

pre_norm_fmul u2(
        .clk(clk),
        .fpu_op(fpu_op_r1),
        .opa(opa_r), .opb(opb_r),
        .fracta(fracta_mul),
        .fractb(fractb_mul),
        .exp_out(exp_mul),
        .sign(sign_mul),
        .sign_exe(sign_exe),
        .inf(), .exp_ovf(), .underflow() // These outputs are not used directly
        );

always @(posedge clk)
    sign_mul_r <= #1 sign_mul;

always @(posedge clk)
    sign_exe_r <= #1 sign_exe;

////////////////////////////////////////////////////////////////////////
// Divide
wire    [49:0]  quo;
wire    [49:0]  fdiv_opa;
wire    [49:0]  remainder;
wire        remainder_00;
reg [4:0]   div_opa_ldz_d, div_opa_ldz_r1, div_opa_ldz_r2;

// Leading zero counter for denormalized opa
always @(*)
    case(fracta_mul[22:0])
       23'b1??????????????????????: div_opa_ldz_d = 1;
       23'b01?????????????????????: div_opa_ldz_d = 2;
       23'b001????????????????????: div_opa_ldz_d = 3;
       23'b0001???????????????????: div_opa_ldz_d = 4;
       23'b00001??????????????????: div_opa_ldz_d = 5;
       23'b000001?????????????????: div_opa_ldz_d = 6;
       23'b0000001????????????????: div_opa_ldz_d = 7;
       23'b00000001???????????????: div_opa_ldz_d = 8;
       23'b000000001??????????????: div_opa_ldz_d = 9;
       23'b0000000001?????????????: div_opa_ldz_d = 10;
       23'b00000000001????????????: div_opa_ldz_d = 11;
       23'b000000000001???????????: div_opa_ldz_d = 12;
       23'b0000000000001??????????: div_opa_ldz_d = 13;
       23'b00000000000001?????????: div_opa_ldz_d = 14;
       23'b000000000000001????????: div_opa_ldz_d = 15;
       23'b0000000000000001???????: div_opa_ldz_d = 16;
       23'b00000000000000001??????: div_opa_ldz_d = 17;
       23'b000000000000000001?????: div_opa_ldz_d = 18;
       23'b0000000000000000001????: div_opa_ldz_d = 19;
       23'b00000000000000000001???: div_opa_ldz_d = 20;
       23'b000000000000000000001??: div_opa_ldz_d = 21;
       23'b0000000000000000000001?: div_opa_ldz_d = 22;
       default: div_opa_ldz_d = 23;
    endcase

assign fdiv_opa = !(|opa_r[30:23]) ? {(fracta_mul<<div_opa_ldz_d), 26'h0} : {fracta_mul, 26'h0};

div_r2 u6(.clk(clk), .opa(fdiv_opa), .opb(fractb_mul), .quo(quo), .rem(remainder));

assign remainder_00 = !(|remainder);

always @(posedge clk)
    div_opa_ldz_r1 <= #1 div_opa_ldz_d;

always @(posedge clk)
    div_opa_ldz_r2 <= #1 div_opa_ldz_r1;

////////////////////////////////////////////////////////////////////////
// Normalize Result
wire        ine_d;
reg [47:0]  fract_denorm;
wire    [47:0]  fract_div;
wire        sign_d;
reg     sign;

always @(posedge clk)
    exp_r <= #1 exp_mul;

assign fract_div = (opb_dn ? quo[49:2] : {quo[26:0], 21'h0});

// Always select the fraction from the divider
always @(*)
    fract_denorm = fract_div;

assign sign_d = sign_mul;

always @(posedge clk)
    sign <= #1 (rmode_r2==2'h3) ? !sign_d : sign_d;

post_norm u4(.clk(clk),
    .fpu_op(fpu_op_r3),
    .opas(opa_r[31]),
    .sign(sign),
    .rmode(rmode_r3),
    .fract_in(fract_denorm),
    .exp_ovf(2'b00), // Not used for Div
    .exp_in(exp_r),
    .opa_dn(opa_dn),
    .opb_dn(opb_dn),
    .rem_00(remainder_00),
    .div_opa_ldz(div_opa_ldz_r2),
    .output_zero(div_00),
    .out(out_d),
    .ine(ine_d),
    .overflow(overflow_d),
    .underflow(underflow_d),
    .f2i_out_sign() // Not used
    );

////////////////////////////////////////////////////////////////////////
// FPU Outputs
wire    [30:0]  out_fixed;
wire        sign_div_final;
wire        ine_div, ine_fasu;
wire        underflow_fasu, underflow_fdiv;
reg     opa_nan_r;

assign div_inf = (fpu_op_r3==3'b011) & (opb_00 | opa_inf);
assign div_00 = (fpu_op_r3==3'b011) & (opa_00 | opb_inf);

assign out_fixed = (qnan_d | snan_d | (fpu_op_r3==3'b011 & opb_00 & opa_00)) ? QNAN : INF;

assign sign_div_final = (sign_exe_r & (opa_inf & opb_inf)) ? !sign_mul_r : sign_mul_r | (opa_00 & opb_00);

always @(posedge clk)
    out <= #1 { ( (fpu_op_r3==3'b011 & !(snan_d | qnan_d)) ?
                       sign_div_final : (snan_d | qnan_d | ind_d) ?
                       nan_sign_d : 1'b0 ),
                ( (div_inf | snan_d | qnan_d) ? out_fixed : out_d )};

// Exception Outputs
assign ine_div  = (ine_d | overflow_d | underflow_d) & !(opb_00 | snan_d | qnan_d | inf_d);
always @(posedge  clk)
    ine <= #1 ine_div;

assign overflow_fdiv = (overflow_d & !(opb_00 | inf_d | snan_d | qnan_d));
always @(posedge clk)
    overflow <= #1 overflow_fdiv;

assign underflow_fasu = underflow_d & !(inf_d | snan_d | qnan_d);
assign underflow_fdiv = underflow_fasu & !opb_00;
always @(posedge clk)
    underflow <= #1 underflow_fdiv;

always @(posedge clk)
    snan <= #1 snan_d;

always @(posedge clk)
    qnan <= #1 snan_d | qnan_d | (opa_00 & opb_00 & fpu_op_r3==3'b011);

always @(posedge clk)
    inf <= #1 (!(qnan_d | snan_d) & (
                ((&out_d[30:23]) & !(|out_d[22:0]) & !(opb_00 & fpu_op_r3==3'b011)) |
                (!opa_00 & opb_00 & fpu_op_r3==3'b011) |
                (fpu_op_r3==3'b011 & opa_inf & !opb_inf)
                  )
            );

wire output_zero_fdiv = (div_00 | (out_d_00 & !opb_00)) & !(opa_inf & opb_inf) &
                        !(opa_00 & opb_00) & !(qnan_d | snan_d);
wire out_d_00 = !(|out_d);

always @(posedge clk)
    zero <= #1 output_zero_fdiv;

always @(posedge clk)
    opa_nan_r <= #1 !opa_nan & fpu_op_r2==3'b011;

always @(posedge clk)
    div_by_zero <= #1 opa_nan_r & !opa_00 & !opa_inf & opb_00;

endmodule