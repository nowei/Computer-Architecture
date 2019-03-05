module fetch(
    input               clk,
    input               do_fetch,
    input       [31:0]  pc,
    output reg  [31:0]  inst
    );
`include "arm32_base.v"

  reg [code_width - 1:0]  code_mem[0:code_words - 1];

// Simplistic test.  For a simple test put these two lines here, and the rf line in the register file.
//  initial begin
  //  code_mem[0] = 32'b1110_000_0100_0_0010_0010_00000000_0001;  // ADD r2, r2, r1
  //  code_mem[1] = 32'b1110_101_0_11111111_11111111_11111101;  // branch -12 which is PC = (PC + 8) - 12 = PC - 4
//end
//  initial begin
//  rf[1] = 32'd1;     // for testing
//end

  initial begin
    $readmemh("testcode/code.hex", code_mem);
  end

  always @(posedge clk) begin
    if (do_fetch)
      inst <= code_mem[pc[code_addr_width - 1 + 2:2]];
  end

endmodule