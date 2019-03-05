module reg_decode(
    input [31:0]    inst,
    input           cond_go,
    output  reg [3:0] rf_rs1,
    output  reg [3:0] rf_rs2,
    output  reg [3:0] rf_rs3,
    output  reg [3:0] rf_ws1,
    output  reg [3:0] rf_ws2,
    output  reg       rf_we1,
    output  reg       rf_we2);

`include "arm32_base.v"

// "Decode" what gets read and written
  always @(*) begin
    rf_rs1 = inst_rn(inst);
    rf_rs2 = inst_rm(inst);

    if (inst_type(inst) == inst_type_sdt)
      rf_rs3 = inst_rd(inst);    
    else
      rf_rs3 = inst_rs(inst);

    if (inst_type(inst) == inst_type_branch_and_link)
      rf_ws1 = r14;
    else
    if (inst_type(inst) == inst_type_data_proc)
      rf_ws1 = inst_rd(inst);
    else
    if (inst_type(inst) == inst_type_sdt && inst_sdt_load(inst) == sdt_is_load)
      rf_ws1 = inst_rd(inst);
    else
      rf_ws1 = inst_rn(inst);

    rf_ws2 = inst_rn(inst);
  end

  // "Decode" whether we write the register file
  always @(*) begin
    rf_we1 = false;
    rf_we2 = false;
    case (inst_type(inst))
        inst_type_branch_and_link:
          rf_we1 = true;
        inst_type_data_proc:
          case (inst_opcode(inst))
            opcode_tst, opcode_cmp, opcode_cmn: rf_we1 = false;
            default:
              if (cond_go)
                rf_we1 = true;
            endcase
        inst_type_sdt:
          if (inst_sdt_load(inst) == sdt_is_load && cond_go)
            rf_we1 = true;
        default:
          rf_we1 = false;
    endcase

    if (inst_type(inst) == inst_type_sdt &&
        inst_sdt_wb(inst) == sdt_is_base_write &&
        cond_go)
      rf_we2 = true;
  end
  
endmodule