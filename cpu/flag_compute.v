module flag_compute(
    input [31:0]    inst,
    input [31:0]    cpsr,
    output reg      cond_go,
    output reg      set_cond_bits
    );

`include "arm32_base.v"

always @(*) begin
    case (inst_cond(inst))
      cond_al:  cond_go = true;
      cond_eq:  cond_go = cpsr[cpsr_z];
      cond_ne:  cond_go = ~cpsr[cpsr_z];
      cond_cs:  cond_go = cpsr[cpsr_c];
      cond_cc:  cond_go = ~cpsr[cpsr_c];
      cond_ns:  cond_go = cpsr[cpsr_n];
      cond_nc:  cond_go = ~cpsr[cpsr_n];
      cond_vs:  cond_go = cpsr[cpsr_v];
      cond_vc:  cond_go = ~cpsr[cpsr_v];
      cond_hi:  cond_go = cpsr[cpsr_c] && (~cpsr[cpsr_z]);
      cond_ls:  cond_go = ~cpsr[cpsr_c] && cpsr[cpsr_z];
      cond_ge:  cond_go = (cpsr[cpsr_n] == cpsr[cpsr_v]) ? true : false;
      cond_lt:  cond_go = (cpsr[cpsr_n] != cpsr[cpsr_v]) ? true : false;
      cond_gt:  cond_go = (~cpsr[cpsr_z] && cpsr[cpsr_n] == cpsr[cpsr_v]) ? true : false;
      cond_le:  cond_go = (cpsr[cpsr_z] && cpsr[cpsr_n] != cpsr[cpsr_v]) ? true : false;
      default:
        cond_go = true;
    endcase
    set_cond_bits = cond_go && inst_type(inst) == inst_type_data_proc && inst_setcond(inst);
  end

endmodule