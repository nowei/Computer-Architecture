module reg_file(
    input   clk,
    input   [3:0] rf_rs1,
    input   [3:0] rf_rs2,
    input   [3:0] rf_rs3,
    input   [3:0] rf_ws1,
    input   [3:0] rf_ws2,
    input   [31:0] rf_wd1,
    input   [31:0] rf_wd2,
    input   rf_we1,
    input   rf_we2,
    input   do_read,
    input   do_write1,
    input   do_write2,
    input   [31:0]  next_cpsr,
    input   set_cond_bits,
    output  wire [31:0] rf_d1,
    output  wire [31:0] rf_d2,
    output  wire [31:0] rf_d3,
    output  wire [31:0] cpsr
    );

`include "arm32_base.v"

// "Register access" and "Writeback"
  reg [31:0]  rf[0:15];          // register 15 is the pc
  reg [31:0]  the_cpsr;

  assign cpsr = the_cpsr;

  always @(*)
    the_cpsr[27:0] = 28'd0;  // most of the cpsr we don't support

  always @(posedge clk) begin 
    if (do_write1 && set_cond_bits) begin
      the_cpsr[cpsr_c] = next_cpsr[cpsr_c];
      the_cpsr[cpsr_n] = next_cpsr[cpsr_n];
      the_cpsr[cpsr_z] = next_cpsr[cpsr_z];
      the_cpsr[cpsr_v] = next_cpsr[cpsr_v];
    end
  end

  reg [31:0]  rf_d1_raw;
  reg [31:0]  rf_d2_raw;
  reg [31:0]  rf_d3_raw;
  reg [31:0] rf_wd;
  reg [3:0] rf_ws;
  reg read_reg_file;
  reg write_reg_file;

  assign rf_d1 = rf_d1_raw;
  assign rf_d2 = rf_d2_raw;
  assign rf_d3 = rf_d3_raw;

  always @(posedge clk) begin
    if (read_reg_file) begin
      rf_d1_raw <= rf[rf_rs1];
      rf_d2_raw <= rf[rf_rs2];
      rf_d3_raw <= rf[rf_rs3];
    end
    if (write_reg_file)
      rf[rf_ws] <= rf_wd;
  end

  always @(*) begin
    read_reg_file = false;
    write_reg_file = false;

    if (do_read)
      read_reg_file = true;

    if (do_write1 && rf_we1) begin
      write_reg_file = true;
      rf_ws = rf_ws1;
      rf_wd = rf_wd1;
    end
    else if (do_write2 && rf_we2) begin
      write_reg_file = true;
      rf_ws = rf_ws2;
      rf_wd = rf_wd2;
    end else begin  // base case, just to avoid latches
      rf_ws = rf_ws1;
      rf_wd = rf_wd1;
    end
  end

  
endmodule