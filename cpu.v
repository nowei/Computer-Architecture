module cpu(
  input wire clk,
  input wire resetn,
  output wire led,
  output wire [7:0] debug_port1,
  output wire [7:0] debug_port2,
  output wire [7:0] debug_port3
  );

localparam data_width = 32;
localparam data_width_l2b = $clog2(data_width / 8);
localparam data_words = 512;
localparam data_words_l2 = $clog2(data_words);
localparam data_addr_width = data_words_l2;

  reg [data_width - 1:0]  data_mem[data_words - 1:0];
  reg [data_width - 1:0]  data_mem_rd;
  reg [data_width - 1:0]  data_mem_wd;
  reg [data_addr_width - 1:0] data_addr;
  reg data_mem_we;

  always @(posedge clk) begin
    if (data_mem_we)
        data_mem[data_addr] <= data_mem_wd;
    data_mem_rd <= data_mem[data_addr];
  end

localparam code_width = 32;
localparam code_width_l2b = $clog2(data_width / 8);
localparam code_words = 512;
localparam code_words_l2 = $clog2(data_words);
localparam code_addr_width = code_words_l2 - code_width_l2b;
  reg [code_width - 1:0]  code_mem[data_words - 1:0];
  reg [code_width - 1:0]  code_mem_rd;
  wire [code_addr_width - 1:0] code_addr;
  reg[5:0] i;
  initial begin
    code_mem[0] = 32'hfa000001; //branch 1010Branchoffset
    code_mem[1] = 32'h00000000; // Show that it branches
    code_mem[2] = 32'h11000400; //add 000 10001 (23)shift(22) (21)imm12(10) (9)Rn(5)(4)Rd(0)
    for (i = 0; i < 30; i = i + 1) begin
      rf[i] = 32'b0;
    end
  end

  always @(posedge clk) begin
    code_mem_rd <= code_mem[code_addr];
  end

  reg [29:0]  pc;

  assign led = pc[1]; // make the LED blink on the low order bit of the PC

  assign debug_port1 = pc[7:0];
  assign debug_port2 = code_mem_rd[7:0];
  assign debug_port3 = data_mem_rd[7:0];

  assign code_addr = pc[code_addr_width - 1:0];

  reg [31:0] rf[0:31];
  reg [31:0] rf_d1;
  reg [31:0] rf_d2;
  reg [4:0] rf_rs1;
  reg [4:0] rf_rs2;
  reg [4:0] rf_ws;
  reg [31:0] rf_wd;
  reg rf_we;

  always @(posedge clk) begin
    rf_d1 <= rf[rf_rs1];
    rf_d2 <= rf[rf_rs2];
    if (!resetn && rf_we)
      rf[rf_ws] <= rf_wd;
  end

  always @(posedge clk) begin
    data_mem_wd <= 0;
    data_addr <= 0;
//   code_addr <= 0;
    data_mem_we <= 0;
    if (!resetn) begin
      pc <= 0;
    end else begin
      data_addr <= pc;

      rf_rs1 <= code_mem_rd[4:0];
      rf_rs2 <= code_mem_rd[9:5];
      rf_ws <= code_mem_rd[14:10];
      rf_we <= code_mem_rd[15];
      rf_wd <= code_mem_rd;

      //code_addr <= pc;
      if (pc > 2) begin
        pc <= 0;
        end
      else begin
        pc <= pc + 1;//rf_d1 + rf_d2 + 1;
        if (code_mem_rd[27:25] == 3'b101) begin // BRANCH
          pc <= pc + {8'b0, code_mem_rd[23:0]};
          data_mem_we <= 1;
          data_mem_wd <= 8;
        end
        if (code_mem_rd[28:24] == 5'b10001) begin // ADD
          rf[rf_rs1] <= rf[rf_rs2] + {20'b0,code_mem_rd[21:10]}; //rd = rn + imm12
          data_mem_we <= 1;
          data_mem_wd <= 16;
        end
      end
    end
  end

endmodule


//Intruction Fetch - obtain inst from program storage
//    Get mem[pc]
//Instruction Decode - Determine required actions and inst size
//    figure out op, operands
//Operand Fetch - Locate and obatin operand data
//    Get X1 + X2 from regfile
//Execute - Compute results or status
//    Set control on ALU (branch, add...)
//Result Store - Deposit results in storage for later use
//    ALU output to regfile at X0
// Next Instruction - Determin successor instruction
//    Update PC = PC + 4
