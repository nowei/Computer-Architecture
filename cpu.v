module cpu(
  input wire clk,
  input wire nreset,
  output wire led,
  output wire [7:0] debug_port1,
  output wire [7:0] debug_port2,
  output wire [7:0] debug_port3
  );
  localparam data_width = 32;
  localparam data_width_l2b = $clog2(data_width / 8);
  localparam data_words = 8;//32;
  localparam data_words_l2 = $clog2(data_words);
  localparam data_addr_width = data_words_l2;

  assign debug_port1 = pc[9:2];
  assign debug_port2 = branch_target[7:0];
  assign debug_port3 = rf[14][7:0];
  //STORE WORKS data_mem[data_addr][7:0]
  //data_mem_wd[7:0] & rf_wd[7:0] keeps disconnecting the USB
  //rf_ws[7:0] correct

  reg [data_width - 1:0]  data_mem[data_words - 1:0];
  reg [data_width - 1:0]  data_mem_rd;
  reg [data_width - 1:0]  data_mem_wd;
  // reg [data_addr_width - 1:0] data_addr_rd; //REDUNDANT both used for same thing
  // reg [data_addr_width - 1:0] data_addr_wd; //but keep just in case for the future
  reg [data_addr_width - 1:0] data_addr; //use instead of the two above
  reg data_mem_we;

  localparam code_width = 32;
  localparam code_width_l2b = $clog2(code_width / 8);
  localparam code_words = 16;
  localparam code_words_l2 = $clog2(code_words);
  localparam code_addr_width = code_words_l2;
  reg [code_width - 1:0]  code_mem[0:code_words - 1];
  wire [code_width - 1:0]  code_mem_rd;
  wire [code_addr_width - 1:0] code_addr;

  localparam r1 = 4'b0001;
  localparam r2 = 4'b0010;
  localparam r3 = 4'b0011;
  localparam r15 = 4'b1111;
  localparam r14 = 4'b1110; //Link Register

  localparam branch_opcode = 4'b1010;
  localparam branchLink_opcode = 4'b1011;
  localparam branchExchange_opcode = 24'b0001_0010_1111_1111_1111_0001;

  localparam IPUBWLbits_ldr = 6'b001001;
  localparam IPUBWLbits_str = 6'b001000;

  localparam do_nothing = 32'h00000000;

  initial begin
  // code_mem[0] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r1}; //ADD r2, r2, r1
  // //code_mem[1] = 32'b1110_101_0_11111111_11111111_11111101;  // unconditional branch -12 which is PC = (PC + 8) - 12 = PC - 4
   code_mem[1] = {cond_al, branch_opcode, 24'd0}; //unconditional branch
   code_mem[3] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r1};
   code_mem[4] = {cond_ne, branch_opcode, 24'd0};//conditional branch BNE
   code_mem[7] = {cond_al, branchLink_opcode, 24'd0}; //BL
   code_mem[10] = {cond_al,inst_type_ldr_str, IPUBWLbits_str, r2, r1, 12'd0}; //STR R2 at R2+0
   code_mem[12] = {cond_al,inst_type_ldr_str, IPUBWLbits_ldr, r3, r1, 12'd0};//LDR R3 with [R2+0]
   code_mem[14] = {cond_al, branchExchange_opcode, r14};

  end

  reg [code_width - 1:0]  pc;
  assign code_addr = pc[code_addr_width - 1 + 2:2];
  assign code_mem_rd = code_mem[code_addr];

  assign led = pc[2]; // make the LED blink on the low order bit of the PC


  reg [31:0] rf[0:14];  // register 15 is the pc
initial begin
  rf[1] <= 32'd1;     // for testing
  // rf[2] <= 32'b0;
  // rf[3] <= 32'd3;
  // rf[r14] <= 32'b0;
end

  reg [31:0] cpsr;    // program status register
  localparam cpsr_n = 31;
  localparam cpsr_z = 30;
  localparam cpsr_c = 29;
  localparam cpsr_v = 28;

  reg [3:0] rf_rs1;
  reg [3:0] rf_rs2;
  reg [3:0] rf_ws;
  reg [31:0] rf_wd;
  reg rf_we;
  wire [31:0] rf_d1;
  wire [31:0] rf_d2;

  assign rf_d1 = (rf_rs1 == r15) ? pc : rf[rf_rs1];
  assign rf_d2 = (rf_rs2 == r15) ? pc : rf[rf_rs2];

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

function automatic inst_rs_isreg;
    input [31:0] inst;
    if (inst[4] == 1'b1 && inst[7] == 1'b0)
      inst_rs_isreg = 1'b1;
    else
      inst_rs_isreg = 1'b0;
endfunction

function automatic [7:0] inst_data_proc_imm;
    input [31:0]  inst;
    inst_data_proc_imm = inst[7:0];
endfunction

function automatic [11:0] inst_ldrstr_imm;
    input [31:0]  inst;
    inst_ldrstr_imm = inst[11:0];
endfunction

localparam operand2_is_reg = 1'b0;
localparam operand2_is_imm  = 1'b1;
function automatic operand2_type;
    input [31:0]  inst;
    operand2_type = inst[25];
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

localparam inst_type_branchLink = 1'b1;
function automatic inst_branch_islink;
    input [31:0]   inst;
    inst_branch_islink = inst[24];
endfunction

//might want this to distinguish for Load/Store Bit
// inst[20] = 1 or Load, = 0 for Store
localparam inst_type_load = 1'b1;
function automatic inst_ldrstr_isload;
    input [31:0]   inst;
    inst_ldrstr_isload = inst[20];
endfunction

function automatic [31:0] inst_branch_imm;
    input [31:0]  inst;
    inst_branch_imm = { {6{inst[23]}}, inst[23:0], 2'b00 };
endfunction

localparam inst_type_branch = 2'b10;
localparam inst_type_data_proc = 2'b00;
localparam inst_type_ldr_str = 2'b01;

function automatic [1:0] inst_type;
    input [31:0]  inst;
    inst_type = inst[27:26];
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
localparam opcode_cmpn = 4'b1011;
localparam opcode_orr = 4'b1100;
localparam opcode_mov = 4'b1101;
localparam opcode_bic = 4'b1110;
localparam opcode_mvn = 4'b1111;
function automatic [3:0] inst_opcode;
    input [31:0]  inst;
    inst_opcode = inst[24:21];
endfunction

// IDEA for control unit
// localparam Reg2Loc, uncondB, Btaken, memRead, memToReg, memWrite, ALUSrc, 
//           RegWrite, ALU_Imm12_control, flag_enable, RegRdSel, BL_signal, BSel;
// localparam [2:0] ALUOp;
// function automatic ctrl_unit;
//   input [3:0] inst_opcode;
//   //begin?
//   if(inst_opcode == opcode_add) begin
//     Reg2Loc  = 1'b1;
//     ALUSrc   = 1'b0;   
//     memtoReg = 1'b0; 
//     RegWrite = 1'b0; // changed this
//     memWrite = 1'b0;
//     memRead  = 1'b0;   
//     Btaken  = 1'b0; 
//     uncondB = 1'bx;
//     ALUOp    = 3'b010;
//     ALU_Imm12_control = 1'b0;
//     flag_enable = 1'b0;
//     RegRdSel = 1'b0;
//     BL_signal = 1'b0;
//     BSel = 1'b0;	
//   end 
// endfunction


///////////////////////////////////////
// FETCH


//  "Fetch" from code memory into instruction bits
  reg [31:0] inst;
  always @(posedge clk) begin
    if (~fd_pipe[32]) begin// checks if valid // MAYBE WE DON'T NEED THISSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS
      fd_pipe[31:0] <= code_mem_rd;
      //Im pretty sure we need to pass in PC to this pipe reg
      fd_pc <= pc; // Maybe this needs to be pc + 4
    end
  end


  reg [32:0] fd_pipe; 
  reg [31:0] fd_pc;

///////////////////////////////////////
// DECODE

// "Decode" the second operand
  reg [31:0] operand2;
  // compute second operand
  always @(posedge clk) begin
    // For now, we only support R type unshifted instructions.
    // shifts and such are NOT implemented.
    if (~fd_pipe[32]) begin
      if (operand2_type(fd_pipe[31:0]) == operand2_is_reg)
        operand2 = rf_d2;
      else
        operand2 = inst_data_proc_imm(fd_pipe[31:0]);
      end
    end

  reg [15:0] in_use;

    // "Decode" what gets read and written
    always @(posedge clk) begin
      if (~fd_pipe[32]) begin
        rf_rs1 = inst_rn(fd_pipe[31:0]);
        rf_rs2 = inst_rm(fd_pipe[31:0]);
        if (inst_branch_islink(fd_pipe[31:0]) == inst_type_branchLink &&
            inst_type(fd_pipe[31:0]) == inst_type_branch)
          rf_ws = r14;
        else if (inst_type(fd_pipe[31:0]) == inst_type_ldr_str) begin
          if (inst_ldrstr_isload(fd_pipe[31:0]) == inst_type_load)
            rf_ws = rf_rs1; 
          end
        else
          rf_ws = inst_rd(fd_pipe[31:0]);
      end
  end

  // "Decode" whether we write the register file
  always @(posedge clk) begin
    if (~fd_pipe[32]) begin
      rf_we = 1'b0;
      data_mem_we = 1'b0;
      case (inst_type(fd_pipe[31:0]))
          inst_type_branch: begin
            // rf_we = 1'b0;
            if (inst_branch_islink(fd_pipe[31:0]) == 1)
              rf_we = 1'b1;
          end

          inst_type_data_proc:
            if (inst_cond(fd_pipe[31:0]) == cond_al)
              rf_we = 1'b1;

          inst_type_ldr_str: begin
            if (inst_ldrstr_isload(fd_pipe[31:0]) == inst_type_load)
              rf_we = 1'b1;
            else
              data_mem_we = 1'b1;
            end
          // default:
          //   rf_we = 1'b1;
      endcase
    end
  end

  // "Decode" the branch target
  reg [31:0] branch_target;
  always @(posedge clk) begin
    if (~fd_pipe[32]) begin
      if(fd_pipe[27:4] == branchExchange_opcode) begin
        branch_target = rf[fd_pipe[3:0]];
      end
      else
        branch_target = fd_pc + 8 + inst_branch_imm(fd_pipe[31:0]);
    end
  end

  always @(posedge clk) begin
    if (~fd_pipe[32]) begin
      de_pipe[31:0] = fd_pipe[31:0]; //<--change this to what we decoded from inst in fd_pip
      //de_pipe[whatever size needed] = {branch_target, data_mem_we, rf_we, rf_rs1(rn), rf_rs2(rm), rf_ws, operand2(?), flush(?), stall(?};
      de_pc <= fd_pc;
    end
  end

  reg [32:0] de_pipe; 
  reg [31:0] de_pc;

///////////////////////////////////////
// EXECUTE

  // "Execute" the instruction
  reg [32:0] alu_result;
  always @(posedge clk) begin
    if (~de_pipe[32]) begin
      if (inst_branch_islink(de_pipe[31:0]) == inst_type_branchLink &&
          inst_type(de_pipe[31:0]) == inst_type_branch)
        alu_result = {1'b0, pc + 4}; // loads LR with next instruction

      else if (inst_type(de_pipe[31:0]) == inst_type_ldr_str) begin
        data_addr = rf[inst_rd(de_pipe[31:0])] + inst_ldrstr_imm(de_pipe[31:0]);
        if (inst_ldrstr_isload(de_pipe[31:0]) == inst_type_load) begin
          // rd is source
          //rf_wd = data_mem[data_addr];
          alu_result = {1'b0,data_mem[data_addr]};
          // writes to rf[inst_rn(inst)]
        end
        else begin // store
          // rd is destination
          data_mem_wd = rf[inst_rn(de_pipe[31:0])]; //this maybe broke it?
          // writes to data_mem[rf[inst_rd(inst)] + inst_ldrstr_imm(inst)]
        end
      end
      else
      begin
        alu_result = 33'h0_0000_0000;
        case (inst_opcode(de_pipe[31:0]))
          opcode_and: alu_result = rf_d1 & operand2;
          opcode_eor: alu_result = (rf_d1 & ~operand2) | (~rf_d1 & operand2);
          opcode_sub: begin
                        alu_result = rf_d1 + ~operand2 + 1;
                        if (de_pipe[20] == 1'b1 && rf_ws != 4'b1111)
                          cpsr[cpsr_v] = ((alu_result < 0 && rf_d1 > 0 && ~operand2 + 1 > 0) ||
                                          (alu_result > 0 && rf_d1 < 0 && ~operand2 + 1 < 0) ? 1 : 0);
                      end
          opcode_rsb: begin
                        alu_result = operand2 + ~rf_d1 + 1;
                        if (inst[20] == 1'b1 && rf_ws != 4'b1111)
                          cpsr[cpsr_v] = ((alu_result < 0 && ~rf_d1 + 1 > 0 && operand2 > 0) ||
                                          (alu_result > 0 && ~rf_d1 + 1 < 0 && operand2 < 0) ? 1 : 0);
                      end
          opcode_add: begin
                        alu_result = rf_d1 + operand2;
                        if (de_pipe[20] == 1'b1 && rf_ws != 4'b1111)
                          cpsr[cpsr_v] = ((alu_result < 0 && rf_d1 > 0 && operand2 > 0) ||
                                          (alu_result > 0 && rf_d1 < 0 && operand2 < 0) ? 1 : 0);
                      end
          opcode_adc: begin
                        alu_result = rf_d1 + operand2 + cpsr[cpsr_c];
                        if (de_pipe[20] == 1'b1 && rf_ws != 4'b1111)
                          cpsr[cpsr_v] = ((alu_result < 0 && rf_d1 > 0 && operand2 > 0) ||
                                          (alu_result > 0 && rf_d1 < 0 && operand2 < 0) ? 1 : 0);
                      end
          opcode_sbc: begin
                        alu_result = rf_d1 + ~operand2 + cpsr[cpsr_c];
                        if (de_pipe[20] == 1'b1 && rf_ws != 4'b1111)
                          cpsr[cpsr_v] = ((alu_result < 0 && rf_d1 > 0 && ~operand2 + 1 > 0) ||
                                          (alu_result > 0 && rf_d1 < 0 && ~operand2 + 1 < 0) ? 1 : 0);
                      end
          opcode_rsc: begin
                        alu_result = operand2 + ~rf_d1 + cpsr[cpsr_c];
                        if (inst[20] == 1'b1 && rf_ws != 4'b1111)
                          cpsr[cpsr_v] = ((alu_result < 0 && ~rf_d1 + 1 > 0 && operand2 > 0) ||
                                          (alu_result > 0 && ~rf_d1 + 1 < 0 && operand2 < 0) ? 1 : 0);
                      end
          opcode_tst: alu_result = rf_d1 & operand2;
          opcode_teq: alu_result = rf_d1 ^ operand2;
          opcode_cmp: begin
                        alu_result = rf_d1 + ~operand2 + 1;
                        if (de_pipe[20] == 1'b1 && rf_ws != 4'b1111)
                          cpsr[cpsr_v] = ((alu_result < 0 && rf_d1 > 0 && ~operand2 + 1> 0) ||
                                          (alu_result > 0 && rf_d1 < 0 && ~operand2 + 1 < 0) ? 1 : 0);
                      end
          opcode_cmpn: begin
                        alu_result = rf_d1 + operand2;
                        if (de_pipe[20] == 1'b1 && rf_ws != 4'b1111)
                          cpsr[cpsr_v] = ((alu_result < 0 && rf_d1 > 0 && operand2 > 0) ||
                                          (alu_result > 0 && rf_d1 < 0 && operand2 < 0) ? 1 : 0);
                      end
          opcode_orr: alu_result = rf_d1 | operand2;
          opcode_mov: alu_result = operand2;
          opcode_bic: alu_result = rf_d1 & ~operand2;
          opcode_mvn: alu_result = 32'hFFFF_FFFF ^ operand2;
        endcase

        // Updates condition bits
        if (de_pipe[20] == 1'b1 && rf_ws != 4'b1111) begin
          cpsr[cpsr_c] = alu_result[32];
          cpsr[cpsr_z] = (alu_result == 33'h0_0000_0000 ? 1 : 0);
          cpsr[cpsr_n] = alu_result[31];
        end
      end

      if (inst_opcode(de_pipe[31:0]) != opcode_tst &&
          inst_opcode(de_pipe[31:0]) != opcode_teq &&
          inst_opcode(de_pipe[31:0]) != opcode_cmp &&
          inst_opcode(de_pipe[31:0]) != opcode_cmpn ||
          inst_branch_islink(de_pipe[31:0]) == 1'b1)
      begin
        // if (inst_type(inst) == inst_type_ldr_str && inst_ldrstr_isload(inst) != inst_type_load)
        //   data_mem_wd = alu_result[31:0];
        // else if (inst_type(inst) == inst_type_ldr_str && inst_ldrstr_isload(inst) == inst_type_load)
        //   rf_wd = data_mem_rd;
        // else
          rf_wd = alu_result[31:0];
      end
    end
  end

  // Executes 
  always @(posedge clk) begin
    // data_mem_wd = 0; //added this in from lab 1 starter from here to
    // data_addr = 0;
  //   code_addr <= 0;
    // data_mem_we = 0; //HERE. made this note just in case anything breaks
    if (~de_pipe[32]) begin
      if (!nreset)
          pc <= 32'd0;
      else begin
        // default behavior
        if (pc > 65) begin
         pc <= 32'd0;
        end else begin
          pc <= pc + 4;
        end
        if (inst_type(de_pipe[31:0]) == inst_type_branch || de_pipe[27:4] == branchExchange_opcode) begin
          case (inst_cond(de_pipe[31:0]))
            cond_eq: if (cpsr[cpsr_z] == 1'b1) pc <= branch_target;
            cond_ne: if (~cpsr[cpsr_z]) pc <= branch_target;
            cond_cs: if (cpsr[cpsr_c]) pc <= branch_target;
            cond_cc: if (~cpsr[cpsr_c]) pc <= branch_target;
            cond_ns: if (cpsr[cpsr_n]) pc <= branch_target;
            cond_nc: if (~cpsr[cpsr_n]) pc <= branch_target;
            cond_vs: if (cpsr[cpsr_v]) pc <= branch_target;
            cond_vc: if (~cpsr[cpsr_v]) pc <= branch_target;
            cond_hi: if (cpsr[cpsr_c] && ~cpsr[cpsr_z]) pc <= branch_target;
            cond_ls: if (~cpsr[cpsr_c] || cpsr[cpsr_z]) pc <= branch_target;
            cond_ge: if (cpsr[cpsr_n] == cpsr[cpsr_v]) pc <= branch_target;
            cond_lt: if (cpsr[cpsr_n] != cpsr[cpsr_v]) pc <= branch_target;
            cond_gt: if (~cpsr[cpsr_z] && cpsr[cpsr_n] == cpsr[cpsr_v]) pc <= branch_target;
            cond_le: if (cpsr[cpsr_z] || cpsr[cpsr_n] != cpsr[cpsr_v]) pc <= branch_target;
            cond_al: pc <= branch_target;
          endcase
            // pc <= branch_target; marks comment
        end
      end
    end
  end

  always @(posedge clk) begin
    fd_pipe[32] <= 1'b0;
    de_pipe[32] <= fd_pipe[32];
    if (~de_pipe[32]) begin
      // *************************************************
      // ADD MORE CONDITIONS SO THAT WE CAN STALL
      // *************************************************
      if (inst_type(de_pipe[31:0]) == inst_type_branch || de_pipe[27:4] == branchExchange_opcode) begin
          case (inst_cond(de_pipe[31:0]))
            cond_eq: if (cpsr[cpsr_z] == 1'b1) begin
                fd_pipe[32] <= 1'b1;
                de_pipe[32] <= 1'b1;
              end
            cond_ne: if (~cpsr[cpsr_z]) begin
                fd_pipe[32] <= 1'b1;
                de_pipe[32] <= 1'b1;
              end
            cond_cs: if (cpsr[cpsr_c]) begin
                fd_pipe[32] <= 1'b1;
                de_pipe[32] <= 1'b1;
              end
            cond_cc: if (~cpsr[cpsr_c]) begin
                fd_pipe[32] <= 1'b1;
                de_pipe[32] <= 1'b1;
              end
            cond_ns: if (cpsr[cpsr_n]) begin
                fd_pipe[32] <= 1'b1;
                de_pipe[32] <= 1'b1;
              end
            cond_nc: if (~cpsr[cpsr_n]) begin
                fd_pipe[32] <= 1'b1;
                de_pipe[32] <= 1'b1;
              end
            cond_vs: if (cpsr[cpsr_v]) begin
                fd_pipe[32] <= 1'b1;
                de_pipe[32] <= 1'b1;
              end
            cond_vc: if (~cpsr[cpsr_v]) begin
                fd_pipe[32] <= 1'b1;
                de_pipe[32] <= 1'b1;
              end
            cond_hi: if (cpsr[cpsr_c] && ~cpsr[cpsr_z]) begin
                fd_pipe[32] <= 1'b1;
                de_pipe[32] <= 1'b1;
              end
            cond_ls: if (~cpsr[cpsr_c] || cpsr[cpsr_z]) begin
                fd_pipe[32] <= 1'b1;
                de_pipe[32] <= 1'b1;
              end
            cond_ge: if (cpsr[cpsr_n] == cpsr[cpsr_v]) begin
                fd_pipe[32] <= 1'b1;
                de_pipe[32] <= 1'b1;
              end
            cond_lt: if (cpsr[cpsr_n] != cpsr[cpsr_v]) begin
                fd_pipe[32] <= 1'b1;
                de_pipe[32] <= 1'b1;
              end
            cond_gt: if (~cpsr[cpsr_z] && cpsr[cpsr_n] == cpsr[cpsr_v]) begin
                fd_pipe[32] <= 1'b1;
                de_pipe[32] <= 1'b1;
              end
            cond_le: if (cpsr[cpsr_z] || cpsr[cpsr_n] != cpsr[cpsr_v]) begin
                fd_pipe[32] <= 1'b1;
                de_pipe[32] <= 1'b1;
              end
            cond_al: begin
                fd_pipe[32] <= 1'b1;
                de_pipe[32] <= 1'b1;
              end
          endcase
            // pc <= branch_target; marks comment
        end
    end
  end

  reg em_rf_we;
  reg [31:0] em_rf_wd;
  reg [3:0] em_rf_ws;
  reg em_data_mem_we;
  reg [data_width - 1:0] em_data_addr;
  reg [data_width - 1:0] em_data_mem_wd;
  always @(posedge clk) begin
    em_pipe <= de_pipe; 
    //em_pipe[probs new size] = {cpsr, alu_result, rf_wd, flush, stall};
    em_rf_we <= rf_we;
    em_rf_wd <= rf_wd;
    em_rf_ws <= rf_ws;
    em_data_mem_we <= data_mem_we;
    em_data_addr <= data_addr;
    em_data_mem_we <= data_mem_we;
  end

  reg [32:0] em_pipe; 

///////////////////////////////////////
// Memory

  always @(posedge clk) begin
    if (~em_pipe[32]) begin
      if (em_data_mem_we)
          data_mem[em_data_addr] <= em_data_mem_wd;
      data_mem_rd <= data_mem[em_data_addr];
    end
  end

  always @(posedge clk) begin
    mwb_pipe <= em_pipe; 
    mwb_rf_we <= em_rf_we;
    mwb_rf_ws <= em_rf_ws;
    mwb_rf_wd <= em_rf_wd;
    //
  end

  reg [32:0] mwb_pipe; 
  reg mwb_rf_we;
  reg [31:0] mwb_rf_wd;
  reg [3:0] mwb_rf_ws;
///////////////////////////////////////
// Write back

  // "Write back" the instruction
  always @(posedge clk) begin
    if (~mwb_pipe[32]) begin
      if (nreset && mwb_rf_we)
        if (mwb_rf_ws != r15) // Also writes from data mem to register
          rf[mwb_rf_ws] <= mwb_rf_wd;
    end
  end

endmodule
