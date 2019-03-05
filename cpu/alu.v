module alu(
    input [31:0]    inst,
    input [32:0]    operand1,
    input [32:0]    operand2,
    input [31:0]    cpsr,
    input           carry_from_shift,
    output reg [32:0]   result,
    output reg [31:0]   next_cpsr,
    output reg [32:0]   adder_result
    );

`include "arm32_base.v"
  // "Execute" the instruction
  reg adder_extra;
  reg [32:0] adder_operand1;
  reg [32:0] adder_operand2;
  reg [32:0] alu_result;

  always @(*) begin
      alu_result = 33'd0;
      next_cpsr = cpsr;
      // This is a little unfortunate but synthesis tools are not always the best at
      // understanding how to re-use the adder.  Nor are they the best at making it
      // an adder/subtractor.  So we pull out the logic and muxes and isolate the adder
      // to a single line below.
      adder_operand1 = operand1;
      adder_operand2 = operand2;
      adder_extra = false;
      if (inst_type(inst) == inst_type_data_proc) begin
        case (inst_opcode(inst))
          opcode_add: begin adder_operand1 = operand1; adder_operand2 = operand2; adder_extra = zero; end
          opcode_sub: begin adder_operand1 = operand1; adder_operand2 = ~operand2; adder_extra = one; end
          opcode_rsb: begin adder_operand1 = operand2; adder_operand2 = ~operand1; adder_extra = one; end
          opcode_adc: begin adder_operand1 = operand1; adder_operand2 = operand2; adder_extra = cpsr[cpsr_c]; end
          opcode_sbc: begin adder_operand1 = operand1; adder_operand2 = ~operand2; adder_extra = cpsr[cpsr_c]; end
          opcode_rsc: begin adder_operand1 = operand2; adder_operand2 = ~operand1; adder_extra = cpsr[cpsr_c]; end
          opcode_cmp: begin adder_operand1 = operand1; adder_operand2 = ~operand2; adder_extra = one; end
          opcode_cmn: begin adder_operand1 = operand1; adder_operand2 = operand2; adder_extra = zero; end
            default: begin adder_operand1 = operand1; adder_operand2 = operand2; adder_extra = zero; end
        endcase
      end
      else if (inst_type(inst) == inst_type_sdt) begin
        if (inst_sdt_up(inst) == sdt_is_up) begin
          adder_operand1 = operand1;
          adder_operand2 = operand2;
          adder_extra = false;
        end
        else begin
          adder_operand1 = operand1;
          adder_operand2 = ~operand2;
          adder_extra = true;
        end
      end      
      adder_result = adder_operand1 + adder_operand2 + { 32'd0, adder_extra };

      if (inst_type(inst) == inst_type_data_proc) begin
        case (inst_opcode(inst))
          opcode_add, opcode_sub, opcode_rsb, opcode_adc,
          opcode_sbc, opcode_rsc, opcode_cmp, opcode_cmn:
              alu_result = adder_result;
          opcode_eor: alu_result = operand1 ^ operand2;
          opcode_and: alu_result = operand1 & operand2;
          opcode_tst: alu_result = operand1 & operand2;
          opcode_teq: alu_result = operand1 ^ operand2;
          opcode_orr: alu_result = operand1 | operand2;
          opcode_mov: alu_result = operand2;
          opcode_bic: alu_result = operand1 & (~operand2);
          opcode_mvn: alu_result = ~operand2;
        endcase
        case (inst_opcode(inst))
          opcode_add, opcode_sub, opcode_rsb, opcode_adc,
          opcode_sbc, opcode_rsc, opcode_cmp, opcode_cmn: begin
            next_cpsr[cpsr_c] = alu_result[32];
            next_cpsr[cpsr_v] = (~operand1[31] && ~operand2[31] && alu_result[31]) |
                                (operand1[31] && operand2[31] && ~alu_result[31]);
          end
          default: begin
            next_cpsr[cpsr_c] = carry_from_shift;
            next_cpsr[cpsr_v] = cpsr[cpsr_v];
          end
        endcase

        next_cpsr[cpsr_n] = alu_result[31];
        next_cpsr[cpsr_z] = (alu_result == 33'd0) ? true : false;
      end
      else begin
        alu_result = adder_result;
      end

      result = alu_result;
  end

endmodule