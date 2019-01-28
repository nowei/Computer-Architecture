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

  initial begin
    //  These are garbage.  You should replace with your code.
    code_mem[0] = 32'hff124500;
    code_mem[1] = 32'hff124501;
    code_mem[2] = 32'hff124567;
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
      if (pc > 2)
        pc <= 0;
      else
        pc <= pc + 1;//rf_d1 + rf_d2 + 1;
    end
  end

endmodule



// TODO: Create this, implement unconditional branch, B,
// and ADD to use the register file. 
/*
    1. inst = code_memory[pc]
    2. pc = pc + 4
    3. if (inst == branch)
    4.     pc = compute_target(pc, inst)

    5. r1 = register_file(rm(inst));
    6. r2 = register_file(rn(inst));
    7. const = constant(inst);
*/
/*
reg [31:0]  register_file[0:31];

wire [31:0] read_result1;
wire [31:0] read_result2;

assign read_result1 = register_file[read_select1];
assign read_result2 = register_file[read_select1];

always @(posedge clock)
 if (register_write_enable)
  register_file[write_select] <= write_data;
*/