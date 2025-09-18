// fcmp_wrapper_pipelined.v
`include "fcmp.v" // Include your original file

module fcmptop(
    // Inputs
    input clk,
    input rst,
    input [31:0] opa_in,
    input [31:0] opb_in,

    // Outputs - Changed to 'reg' to make them registered
    output reg unordered,
    output reg altb,
    output reg blta,
    output reg aeqb,
    output reg inf,
    output reg zero
);

    // --- Stage 1: Input Registers ---
    reg [31:0] opa_reg, opb_reg;

    // This block creates flip-flops for the inputs
    always @(posedge clk) begin
        if (rst) begin
            opa_reg <= 32'b0;
            opb_reg <= 32'b0;
        end else begin
            opa_reg <= opa_in;
            opb_reg <= opb_in;
        end
    end

    // --- Intermediate Wires for Combinational Logic Output ---
    // These wires hold the result from the fcmp unit before it's registered.
    wire unordered_wire, altb_wire, blta_wire, aeqb_wire, inf_wire, zero_wire;

    // Instantiate your original combinational module
    fcmp u_fcmp (
        .opa(opa_reg),      // Use the registered inputs from Stage 1
        .opb(opb_reg),      // Use the registered inputs from Stage 1
        .unordered(unordered_wire), // Connect to intermediate wires
        .altb(altb_wire),
        .blta(blta_wire),
        .aeqb(aeqb_wire),
        .inf(inf_wire),
        .zero(zero_wire)
    );

    // --- Stage 2: Output Registers ---
    // This new block creates flip-flops for the outputs.
    always @(posedge clk) begin
        if (rst) begin
            // On reset, set a defined initial state for all outputs.
            unordered <= 1'b0;
            altb      <= 1'b0;
            blta      <= 1'b0;
            aeqb      <= 1'b0;
            inf       <= 1'b0;
            zero      <= 1'b0;
        end else begin
            // On the next clock edge, capture the result from the combinational logic.
            unordered <= unordered_wire;
            altb      <= altb_wire;
            blta      <= blta_wire;
            aeqb      <= aeqb_wire;
            inf       <= inf_wire;
            zero      <= zero_wire;
        end
    end

endmodule