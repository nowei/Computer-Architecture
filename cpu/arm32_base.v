// Useful macros to make the code more readable
localparam true = 1'b1;
localparam false = 1'b0;
localparam one = 1'b1;
localparam zero = 1'b0;

// Configuration of the processor
localparam little_endian = 0;
localparam big_endian = 1;
localparam endian = little_endian;

// dedicate a region of the address space for I/O.  Specifically, we use  
// 64K of data at the top of the address range for this.  Could be anywhere
// but putting it at the top is easy and out of the way.
localparam mmio_mask = 32'hffff0000;

localparam data_banks = 4;
localparam data_words = 2048;       // Support for 4K (code) + 4K data
localparam data_words_l2 = $clog2(data_words);
localparam data_banks_l2 = $clog2(data_banks);
localparam data_addr_width = data_words_l2 + data_banks_l2;

localparam code_width = 32;
localparam code_width_l2b = $clog2(code_width / 8);
localparam code_words = 1024;         // Support for 4K worth of code
localparam code_words_l2 = $clog2(code_words);
localparam code_addr_width = code_words_l2;


// Functions to help decode the ARM32 instruction set
function automatic [3:0] inst_rn;
  input [31:0] inst;
  inst_rn = inst[19:16];
endfunction

function automatic [3:0] inst_rd;
  input [31:0] inst;
  inst_rd = inst[15:12];
endfunction

function automatic [3:0] inst_rs;
  input [31:0] inst;
  inst_rs = inst[11:8];
endfunction

function automatic [3:0] inst_rm;
  input [31:0] inst;
  inst_rm = inst[3:0];
endfunction

function automatic [31:0] inst_data_proc_imm;
    input [31:0]  inst;
    inst_data_proc_imm = { 24'd0, inst[7:0] };
endfunction

function automatic [31:0] inst_sdt_imm;
    input [31:0]  inst;
    inst_sdt_imm = { 20'd0, inst[11:0] };
endfunction

localparam sdt_is_post = false;
localparam sdt_is_pre = true;
function automatic inst_sdt_pre;
    input [31:0]  inst;
    inst_sdt_pre = inst[24];
endfunction

localparam sdt_is_down = false;
localparam sdt_is_up = true;
function automatic inst_sdt_up;
    input [31:0]  inst;
    inst_sdt_up = inst[23];
endfunction

localparam sdt_is_word = zero;
localparam sdt_is_byte = one;
function automatic inst_sdt_byte;
    input [31:0]  inst;
    inst_sdt_byte = inst[22];
endfunction

localparam sdt_is_no_base_write = zero;
localparam sdt_is_base_write = one;
function automatic inst_sdt_wb;
    input [31:0]  inst;
    inst_sdt_wb = inst[21];
endfunction

localparam sdt_is_store = zero;
localparam sdt_is_load = one;
function automatic inst_sdt_load;
    input [31:0]  inst;
    inst_sdt_load = inst[20];
endfunction

localparam sdt_is_reg = one;
localparam sdt_is_imm = zero;
function automatic inst_sdt_operand_type;
  input [31:0] inst;
  inst_sdt_operand_type = inst[25];
endfunction

localparam data_proc_operand2_is_reg = zero;
localparam data_proc_operand2_is_imm  = one;
function automatic data_proc_operand2_type;
    input [31:0]  inst;
    data_proc_operand2_type = inst[25];
endfunction

localparam shift_reg = true;
localparam shift_imm = false;
function automatic shift_source;
    input [31:0]  inst;
    shift_source = inst[4];
endfunction

localparam shift_type_ll = 2'b00;
localparam shift_type_lr = 2'b01;
localparam shift_type_ar = 2'b10;
localparam shift_type_rr = 2'b11;
function automatic [1:0] shift_type;
    input [31:0]  inst;
    shift_type = inst[6:5];
endfunction

function automatic [4:0] shift_amount_shifted_imm;
  input [31:0]  inst;
  shift_amount_shifted_imm = { inst[11:8], zero };
endfunction

function automatic [4:0] shift_amount_shifted_reg;
  input [31:0]  inst;
  shift_amount_shifted_reg = inst[11:7];
endfunction

localparam cond_eq = 4'b0000;
localparam cond_ne = 4'b0001;
localparam cond_cs = 4'b0010;
localparam cond_cc = 4'b0011;
localparam cond_ns = 4'b0100;
localparam cond_nc = 4'b0101;
localparam cond_vs = 4'b0110;
localparam cond_vc = 4'b0111;
localparam cond_hi = 4'b1000;
localparam cond_ls = 4'b1001;
localparam cond_ge = 4'b1010;
localparam cond_lt = 4'b1011;
localparam cond_gt = 4'b1100;
localparam cond_le = 4'b1101;
localparam cond_al = 4'b1110;
function automatic [3:0] inst_cond;
    input [31:0]  inst;
    inst_cond = inst[31:28];
endfunction

function automatic inst_branch_islink;
    input [31:0]  inst;
    inst_branch_islink = inst[24];
endfunction

function automatic [31:0] inst_branch_imm;
    input [31:0]  inst;
    inst_branch_imm = { {6{inst[23]}}, inst[23:0], 2'b00 };
endfunction

localparam inst_type_branch = 4'b1010;
localparam inst_type_branch_and_link = 4'b1011;
localparam inst_type_data_proc = 4'b0010;
localparam inst_type_branch_and_exchange = 4'b1110;
localparam inst_type_sdt = 4'b0100;
localparam inst_type_not_implemented = 4'b1111;
function automatic [3:0] inst_type;
    input [31:0]  inst;

    reg [3:0] res;

    res = inst_type_not_implemented;
    case (inst[27:25])
      3'b010: res = inst_type_sdt;
      3'b011: res = inst_type_sdt;
      3'b001: res = inst_type_data_proc;
      3'b101:
        if (inst[24])
          res = inst_type_branch_and_link;
        else
          res = inst_type_branch;
      3'b000:
        if (inst[24:20] == 5'b10010)
          res = inst_type_branch_and_exchange;
        else
          res = inst_type_data_proc;
      default:
        res = inst_type_not_implemented;
    endcase
    inst_type = res;
endfunction

localparam opcode_and = 4'b0000;
localparam opcode_eor = 4'b0001;
localparam opcode_sub = 4'b0010;
localparam opcode_rsb = 4'b0011;
localparam opcode_add = 4'b0100;
localparam opcode_adc = 4'b0101;
localparam opcode_sbc = 4'b0110;
localparam opcode_rsc = 4'b0111;
localparam opcode_tst = 4'b1000;
localparam opcode_teq = 4'b1001;
localparam opcode_cmp = 4'b1010;
localparam opcode_cmn = 4'b1011;
localparam opcode_orr = 4'b1100;
localparam opcode_mov = 4'b1101;
localparam opcode_bic = 4'b1110;
localparam opcode_mvn = 4'b1111;
function automatic [3:0] inst_opcode;
    input [31:0]  inst;
    inst_opcode = inst[24:21];
endfunction

function automatic inst_setcond;
    input [31:0]  inst;
    inst_setcond = inst[20];
endfunction

  localparam r15 = 4'b1111;
  localparam r14 = 4'b1110;  
  localparam cpsr_n = 31;
  localparam cpsr_z = 30;
  localparam cpsr_c = 29;
  localparam cpsr_v = 28;

