`timescale 1ns / 100ps

// Single-DUT AES-256 harness (no assume/assert/anyconst).
// - Tiny public inputs for plaintext and key
// - One secret bit perturbs one key byte
// - "done_o" pulses on the first cycle the output becomes stable
// - Exposes full ciphertext for debugging/analysis
module aes256_ct_tb (
  input         clk,

  // Public knobs (keep SMT space small)
  input  [7:0]  state_lo0_i,  // 8b of plaintext control
  input  [7:0]  state_lo1_i,  // 8b of plaintext control
  input  [7:0]  key_lo0_i,    // 8b of key control
  input  [7:0]  key_lo1_i,    // 8b of key control

  // Secret (timing should NOT depend on this)
  input         secret_bit_i,

  // Observables
  output        done_o,        // first-stable pulse (data-driven "done")
  output [127:0] out_o         // ciphertext
);

  // -----------------------------
  // Reduced 128-bit state (plaintext)
  // -----------------------------
  wire [127:0] state_small =
    { 96'h00112233445566778899AABB,  // fixed pattern to shrink space
      state_lo1_i, state_lo0_i };    // 16 public bits

  // -----------------------------
  // Reduced 256-bit key
  //   base 32b from two bytes + const; replicate ×8
  //   secret flips lowest byte when secret_bit_i = 1
  // -----------------------------
  wire [31:0]  key_base   = { key_lo1_i, key_lo0_i, 16'hA5_5A };
  wire [255:0] key_repl   = { key_base, key_base, key_base, key_base,
                              key_base, key_base, key_base, key_base };

  wire [255:0] secret_mask = { 248'd0, (secret_bit_i ? 8'hFF : 8'h00) };
  wire [255:0] key_small   = key_repl ^ secret_mask;

  // -----------------------------
  // DUT
  // -----------------------------
  wire [127:0] out;
  aes_256 dut (
    .clk  (clk),
    .state(state_small),
    .key  (key_small),
    .out  (out)
  );

  assign out_o = out;

  // -----------------------------
  // Data-driven "done" detection:
  //   done = first cycle where out == $past(out)
  //   (i.e., stops changing with static inputs)
  // -----------------------------
  reg [127:0] out_q = 128'h0;
  reg         seen_change = 1'b0;
  reg         done_latched = 1'b0;

  wire changed = (out != out_q);
  wire done_pulse = (seen_change & ~changed) & ~done_latched;

  always @(posedge clk) begin
    out_q <= out;
    // remember if output ever changed since t0
    seen_change <= seen_change | changed;
    // one-shot: latch after first stability pulse
    if (done_pulse)
      done_latched <= 1'b1;
  end

  assign done_o = done_pulse;

endmodule
