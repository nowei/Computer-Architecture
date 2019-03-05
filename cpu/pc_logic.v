module pc_logic(
    input           clk,
    input           nreset,
    input [31:0]    inst,
    input [31:0]    rf_d2,
    input           rf_we1,
    input [3:0]     rf_ws1,
    input [31:0]    rf_wd1,
    input           rf_we2,
    input [3:0]     rf_ws2,
    input [31:0]    rf_wd2,
    input           cond_go,
    input           do_update,
    output reg [31:0] pc,
    output reg [31:0] pc_plus4,
    output reg [31:0] pc_plus8,
    output reg [31:0] pc_plus12);

`include "arm32_base.v"

  
  reg [31:0] pc;
  reg [31:0] branch_target;

  always @(*) begin
    pc_plus4 = pc + 4;
    pc_plus8 = pc + 8;
    pc_plus12 = pc + 12;
    if (inst_type(inst) == inst_type_branch_and_exchange)
      branch_target = rf_d2;
    else
      branch_target = pc_plus8 + inst_branch_imm(inst);
  end

  always @(posedge clk) begin
    if (!nreset) begin
        pc <= 32'd0;
    end
    else begin
      if (do_update) begin
        if ((inst_type(inst) == inst_type_branch ||
            inst_type(inst) == inst_type_branch_and_link ||
            inst_type(inst) == inst_type_branch_and_exchange) && cond_go)
          pc <= branch_target;
        else
        if (rf_we1 && rf_ws1 == r15 && cond_go)
          pc <= rf_wd1;
        else
        if (rf_we2 && rf_ws2 == r15 && cond_go)
          pc <= rf_wd2;
        else
          pc <= pc_plus4;
      end
    end
  end

endmodule