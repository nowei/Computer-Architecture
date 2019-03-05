module shifter(
    input [31:0]    inst,
    input [31:0]    register_input,
    input [31:0]    shift_register_input,
    input           in_cpsr_c,
    output reg [32:0]   shifter_output,
    output reg          carry_from_shift
    );

`include "arm32_base.v"

  reg [33:0] pre_shift_operand2;
  reg [33:0] post_shift_operand2;
  reg [31:0] operand2_rr;
  reg [4:0]  shift_amount;
  reg rr_carry;
  always @(*) begin
    if (inst_type(inst) == inst_type_data_proc) begin
      if (data_proc_operand2_type(inst) == data_proc_operand2_is_reg)
        pre_shift_operand2 = { zero, register_input, zero };
      else
        pre_shift_operand2 = { zero, inst_data_proc_imm(inst), zero };
    end else begin
      if (inst_sdt_operand_type(inst) == sdt_is_reg)
        pre_shift_operand2 = { zero, register_input, zero };
      else
        pre_shift_operand2 = { zero, inst_sdt_imm(inst), zero };
    end
    
    if (inst_type(inst) == inst_type_data_proc) begin
      if (data_proc_operand2_type(inst) == data_proc_operand2_is_reg) begin
        if (shift_source(inst) == shift_reg)
          shift_amount = shift_register_input[4:0];
        else
          shift_amount = shift_amount_shifted_reg(inst);
      end else begin
        shift_amount = shift_amount_shifted_imm(inst);
      end
    end else
    if (inst_type(inst) == inst_type_sdt) begin
        shift_amount = shift_amount_shifted_reg(inst);
    end else
      shift_amount = 5'd0;

    rr_carry = zero;
    operand2_rr = 32'd0;
    if (inst_type(inst) == inst_type_data_proc &&
        data_proc_operand2_type(inst) == data_proc_operand2_is_reg &&
        shift_source(inst) == shift_reg &&
        shift_amount == 5'd0) begin
      if (shift_type(inst) == shift_type_rr) begin
        post_shift_operand2 = { in_cpsr_c, pre_shift_operand2[32:1], zero };
        carry_from_shift = pre_shift_operand2[1];
      end else begin
        post_shift_operand2 = pre_shift_operand2;
        carry_from_shift = in_cpsr_c;
      end
    end else begin
      operand2_rr = (pre_shift_operand2[32:1] >> shift_amount) |
                    (pre_shift_operand2[32:1] << (6'b100000 + { one, ~shift_amount } + 6'b000001));
      rr_carry = operand2_rr[31];       
      if (inst_type(inst) == inst_type_sdt ||
          (inst_type(inst) == inst_type_data_proc &&
           data_proc_operand2_type(inst) == data_proc_operand2_is_reg)) begin
          case (shift_type(inst))
            shift_type_ll: begin
              post_shift_operand2 = pre_shift_operand2 << shift_amount;
              carry_from_shift = post_shift_operand2[33];
            end
            shift_type_lr: begin
              if (shift_amount != 5'd0) begin
                post_shift_operand2 = pre_shift_operand2 >> shift_amount;
                carry_from_shift = post_shift_operand2[0];
              end else begin
                post_shift_operand2 = 34'd0;
                carry_from_shift = pre_shift_operand2[32];
              end
            end
            shift_type_ar: begin
              post_shift_operand2 = { zero, ($signed(pre_shift_operand2[32:0]) >>> shift_amount) };
              carry_from_shift = post_shift_operand2[0];
            end
            shift_type_rr: begin
              post_shift_operand2 = { zero, operand2_rr, zero };
              carry_from_shift = rr_carry;
            end
          endcase
      end else begin
        post_shift_operand2 = { zero, operand2_rr, zero };
        carry_from_shift = rr_carry;
      end
    end

    shifter_output = { zero, post_shift_operand2[32:1] };

    if (inst_type(inst) == inst_type_sdt &&
        inst_sdt_operand_type(inst) == sdt_is_imm) begin
       shifter_output = { zero, inst_sdt_imm(inst) };
       carry_from_shift = in_cpsr_c;
    end
  end

endmodule