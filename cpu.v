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
  assign debug_port2 = rf[2][7:0];//em_data_mem_we[7:0];//rf[2][7:0];//data_mem_rd;
  assign debug_port3 = rf[3][7:0];//em_data_addr[7:0];//data_mem_rd[7:0];//rf[3][7:0];
  //STORE WORKS data_mem[data_addr][7:0]
  //data_mem_wd[7:0] & rf_wd[7:0] keeps disconnecting the USB
  //rf_ws[7:0] correct
  reg [7:0] reading;
  always @(posedge clk) begin
    reading <= rf_d1_df[7:0];
  end
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
  localparam r4 = 4'b0100;
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
   // code_mem[1] = {cond_al, branch_opcode, 24'd0}; //unconditional branch
   // code_mem[3] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r1};
   // code_mem[4] = {cond_ne, branch_opcode, 24'd0};//conditional branch BNE
   // code_mem[7] = {cond_al, branchLink_opcode, 24'd0}; //BL
   // code_mem[10] = {cond_al,inst_type_ldr_str, IPUBWLbits_str, r2, r1, 12'd0}; //STR R2 at R2+0
   // code_mem[12] = {cond_al,inst_type_ldr_str, IPUBWLbits_ldr, r3, r1, 12'd0};//LDR R3 with [R2+0]
   // code_mem[14] = {cond_al, branchExchange_opcode, r14};

    // code_mem[0] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r1}; //ADD r2, r2, r1 = 1 so r2 = 1
    // code_mem[1] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r2}; //ADD r2, r2, r1 = 1 so now r2 = 2
    // code_mem[2] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r2}; //ADD r2, r2, r1 = 1 so now r2 = 2
    // code_mem[3] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r2}; //ADD r2, r2, r1 = 1 so now r2 = 2
    // // code_mem[2] = {cond_al,inst_type_ldr_str, IPUBWLbits_str, r2, r2, 12'd0}; //STR R2 at [R2+0]
    // // code_mem[3] = {cond_al,inst_type_ldr_str, IPUBWLbits_ldr, r3, r2, 12'd0};//LDR R3 with [R2+0] r3 = 2
    // code_mem[4] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r2}; //ADD r2, r2, r1 = 1 so now r2 = 2
    // code_mem[5] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r2}; //ADD r2, r2, r1 = 1 so now r2 = 2
    // code_mem[6] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r2}; //ADD r2, r2, r1 = 1 so now r2 = 2
    // code_mem[7] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r2}; //ADD r2, r2, r1 = 1 so now r2 = 2
    // code_mem[8] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r2}; //ADD r2, r2, r1 = 1 so now r2 = 2
    // code_mem[9] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r2}; //ADD r2, r2, r1 = 1 so now r2 = 2
    // code_mem[10] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r2}; //ADD r2, r2, r1 = 1 so now r2 = 2
    // code_mem[11] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r2}; //ADD r2, r2, r1 = 1 so now r2 = 2
    // code_mem[12] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r2}; //ADD r2, r2, r1 = 1 so now r2 = 2
    // // code_mem[2] = {cond_al,inst_type_ldr_str, IPUBWLbits_str, r2, r2, 12'd0}; //STR R2 at [R2+0]
    // // code_mem[3] = {cond_al,inst_type_ldr_str, IPUBWLbits_ldr, r3, r2, 12'd0};//LDR R3 with [R2+0] r3 = 2
    // // code_mem[4] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r3}; //ADD r2, r2, r3 = 2 so r2 = 4
    // // code_mem[5] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r1}; //ADD r3, r3, r2 = 4 so now r3 = 6

    //Branches taken and untaken
    code_mem[1] = {cond_al, branch_opcode, 24'd1}; //unconditional B taken
    code_mem[2] = {cond_al, 3'b000, opcode_add, 1'b0, r3, r3, 8'b00000000, r1}; //branched over ie no op
    code_mem[3] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r1}; //branched over ie no op
    code_mem[6] = {cond_eq, branchLink_opcode, 24'd0}; //BL untaken
    //Data forwarding
    code_mem[9] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r1}; //ADD r2, r2, r1 @r2 = 1
    code_mem[10] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r1};//ADD r2, r2, r1 @r2 = 2
    code_mem[11] = {cond_al, 3'b000, opcode_add, 1'b0, r2, r2, 8'b00000000, r2};//ADD r2, r2, r2 @r2 = 4
    //Memory load Hazards
    code_mem[12] = {cond_al,inst_type_ldr_str, IPUBWLbits_str, r2, r1, 12'd0};  //STR r2, [r1 + 0] @mem[r2 + 0] = 4 first time around
    code_mem[13] = {cond_al,inst_type_ldr_str, IPUBWLbits_ldr, r3, r1, 12'd0};  //LDR r3, [r1 + 0] @r3 = 4 first time around, matches r2 later
  end

  reg [code_width - 1:0]  pc;
  assign code_addr = pc[code_addr_width - 1 + 2:2];
  assign code_mem_rd = code_mem[code_addr];

  assign led = pc[2]; // make the LED blink on the low order bit of the PC


  reg [31:0] rf[0:14];  // register 15 is the pc
initial begin
  rf[1] <= 32'd1;     // for testing
  // rf[2] <= 32'd1;
  // rf[3] <= 32'd3;
  //rf[4] <= 32'd2;
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

  // Pipe-lined data
  reg [31:0] fd_pipe;
  reg [31:0] fd_pc;
  reg fd_invalid;

  reg [31:0] de_pipe;
  reg [31:0] de_pc;
  reg de_invalid;
  
  reg [31:0] em_pipe;
  reg em_rf_we;
  reg em_invalid;
  reg [3:0] em_rf_ws;
  reg em_data_mem_we;
  reg [data_width - 1:0] em_data_addr;
  //reg [data_width - 1:0] em_data_mem_wd;

  //reg [31:0] mwb_pipe;
  reg mwb_rf_we;
  reg mwb_invalid;
  reg [31:0] mwb_rf_wd;
  reg [3:0] mwb_rf_ws;

  assign rf_d1 = (rf_rs1 == r15) ? pc : rf[rf_rs1];
  assign rf_d2 = (rf_rs2 == r15) ? pc : rf[rf_rs2];

  wire [31:0] rf_d1_df; // This is pretty jank
  wire [31:0] rf_d2_df;
  assign rf_d1_df = (rf_rs1 == em_rf_ws && em_rf_we) ? rf_wd : ((rf_rs1 == mwb_rf_ws && mwb_rf_we) ? mwb_rf_wd : rf_d1);
  assign rf_d2_df = (rf_rs2 == em_rf_ws && em_rf_we) ? rf_wd : ((rf_rs2 == mwb_rf_ws && mwb_rf_we) ? mwb_rf_wd : rf_d2);

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


///////////////////////////////////////
// FETCH

//  "Fetch" from code memory into instruction bits
  // reg [31:0] inst;
  always @(posedge clk) begin
    if (~fd_invalid) begin// checks if valid // MAYBE WE DON'T NEED THISSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS
      fd_pipe <= code_mem_rd;
      // inst <= code_mem_rd;
      //Im pretty sure we need to pass in PC to this pipe reg
      fd_pc <= pc + 4; // Maybe this needs to be pc + 4
    end
  end


///////////////////////////////////////
// DECODE

// "Decode" the second operand
  reg [31:0] operand2;
  // compute second operand
  always @(*) begin
    // For now, we only support R type unshifted instructions.
    // shifts and such are NOT implemented.
    if (~fd_invalid) begin
      if (operand2_type(fd_pipe) == operand2_is_reg)
        operand2 = rf_d2_df;
      else
        operand2 = inst_data_proc_imm(fd_pipe);
      end
    end

    // "Decode" what gets read and written
    always @(*) begin
      if (~fd_invalid) begin
        rf_rs1 = inst_rn(fd_pipe);
        rf_rs2 = inst_rm(fd_pipe);
        if (inst_branch_islink(fd_pipe) == inst_type_branchLink &&
            inst_type(fd_pipe) == inst_type_branch)
          rf_ws = r14;
        else if (inst_type(fd_pipe) == inst_type_ldr_str) begin
          if (inst_ldrstr_isload(fd_pipe) == inst_type_load)
            rf_ws = rf_rs1;
          end
        else
          rf_ws = inst_rd(fd_pipe);
      end
  end

  // "Decode" whether we write the register file
  always @(*) begin
    if (~fd_invalid) begin
      rf_we = 1'b0;
      data_mem_we = 1'b0;
      case (inst_type(fd_pipe))
          inst_type_branch: begin
            // rf_we = 1'b0;
            if (inst_branch_islink(fd_pipe) == 1)
              rf_we = 1'b1;
          end

          inst_type_data_proc:
            if (inst_cond(fd_pipe) == cond_al)
              rf_we = 1'b1;

          inst_type_ldr_str: begin
            if (inst_ldrstr_isload(fd_pipe) == inst_type_load)
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
  always @(*) begin
    if (~fd_invalid) begin
      if(fd_pipe[27:4] == branchExchange_opcode) begin
        branch_target = rf[fd_pipe[3:0]];
      end
      else
        branch_target = fd_pc + 8 + inst_branch_imm(fd_pipe);
    end
  end


  always @(*) begin
    if (~de_invalid) begin
      de_pipe = fd_pipe; //<--change this to what we decoded from inst in fd_pip
      //de_pipe[whatever size needed] = {branch_target, data_mem_we, rf_we, rf_rs1(rn), rf_rs2(rm), rf_ws, operand2(?), flush(?), stall(?};
      de_pc <= fd_pc;
    end
  end


///////////////////////////////////////
// EXECUTE

  // "Execute" the instruction
  reg [32:0] alu_result;
  always @(posedge clk) begin
    if (~de_invalid) begin
      if (inst_branch_islink(de_pipe) == inst_type_branchLink &&
          inst_type(de_pipe) == inst_type_branch)
        alu_result = {1'b0, pc + 4}; // loads LR with next instruction

      else if (inst_type(de_pipe) == inst_type_ldr_str) begin
        data_addr = rf[inst_rd(de_pipe)] + inst_ldrstr_imm(de_pipe);



        // CHANGED HEREEEEEEEEEEEEEEEEEEEEEE

        // DON'T WRITE into ALU_RESULT because current read of data_mem is wrong
        // due to it being updated after memory (think about instruction where we
        // store and then load immediately after. Writing alu_result will give old
        // value rather than the new one. To fix this, we delay the read until the
        // memory access stage.

        // if (inst_ldrstr_isload(de_pipe) == inst_type_load) begin
        //   // rd is source
        //   //rf_wd = data_mem[data_addr];
        //   alu_result = {1'b0,data_mem[data_addr]};
        //   // writes to rf[inst_rn(inst)]
        // end
  // assign rf_d1_df = (rf_rs1 == em_rf_ws && em_rf_we) ? rf_wd : ((rf_rs1 == mwb_rf_ws && mwb_rf_we) ? mwb_rf_wd : rf_d1);

        if (inst_ldrstr_isload(de_pipe) != inst_type_load) begin // store
          // rd is destination
          if (inst_rn(de_pipe) == em_rf_ws)
            data_mem_wd = rf_wd;
          else if (inst_rn(de_pipe) == mwb_rf_ws)
            data_mem_wd = mwb_rf_wd;
          else
            data_mem_wd = rf[inst_rn(de_pipe)];
          // writes to data_mem[rf[inst_rd(inst)] + inst_ldrstr_imm(inst)]
        end






      end
      else
      begin
        alu_result = 33'h0_0000_0000;
        case (inst_opcode(de_pipe))
          opcode_and: alu_result = rf_d1_df & operand2;
          opcode_eor: alu_result = (rf_d1_df & ~operand2) | (~rf_d1_df & operand2);
          opcode_sub: begin
                        alu_result = rf_d1_df + ~operand2 + 1;
                        if (de_pipe[20] == 1'b1 && rf_ws != 4'b1111)
                          cpsr[cpsr_v] = ((alu_result < 0 && rf_d1_df > 0 && ~operand2 + 1 > 0) ||
                                          (alu_result > 0 && rf_d1_df < 0 && ~operand2 + 1 < 0) ? 1 : 0);
                      end
          opcode_rsb: begin
                        alu_result = operand2 + ~rf_d1_df + 1;
                        if (de_pipe[20] == 1'b1 && rf_ws != 4'b1111)
                          cpsr[cpsr_v] = ((alu_result < 0 && ~rf_d1_df + 1 > 0 && operand2 > 0) ||
                                          (alu_result > 0 && ~rf_d1_df + 1 < 0 && operand2 < 0) ? 1 : 0);
                      end
          opcode_add: begin
                        alu_result = rf_d1_df + operand2;
                        if (de_pipe[20] == 1'b1 && rf_ws != 4'b1111)
                          cpsr[cpsr_v] = ((alu_result < 0 && rf_d1_df > 0 && operand2 > 0) ||
                                          (alu_result > 0 && rf_d1_df < 0 && operand2 < 0) ? 1 : 0);
                      end
          opcode_adc: begin
                        alu_result = rf_d1_df + operand2 + cpsr[cpsr_c];
                        if (de_pipe[20] == 1'b1 && rf_ws != 4'b1111)
                          cpsr[cpsr_v] = ((alu_result < 0 && rf_d1_df > 0 && operand2 > 0) ||
                                          (alu_result > 0 && rf_d1_df < 0 && operand2 < 0) ? 1 : 0);
                      end
          opcode_sbc: begin
                        alu_result = rf_d1_df + ~operand2 + cpsr[cpsr_c];
                        if (de_pipe[20] == 1'b1 && rf_ws != 4'b1111)
                          cpsr[cpsr_v] = ((alu_result < 0 && rf_d1_df > 0 && ~operand2 + 1 > 0) ||
                                          (alu_result > 0 && rf_d1_df < 0 && ~operand2 + 1 < 0) ? 1 : 0);
                      end
          opcode_rsc: begin
                        alu_result = operand2 + ~rf_d1_df + cpsr[cpsr_c];
                        if (de_pipe[20] == 1'b1 && rf_ws != 4'b1111)
                          cpsr[cpsr_v] = ((alu_result < 0 && ~rf_d1_df + 1 > 0 && operand2 > 0) ||
                                          (alu_result > 0 && ~rf_d1_df + 1 < 0 && operand2 < 0) ? 1 : 0);
                      end
          opcode_tst: alu_result = rf_d1_df & operand2;
          opcode_teq: alu_result = rf_d1_df ^ operand2;
          opcode_cmp: begin
                        alu_result = rf_d1_df + ~operand2 + 1;
                        if (de_pipe[20] == 1'b1 && rf_ws != 4'b1111)
                          cpsr[cpsr_v] = ((alu_result < 0 && rf_d1_df > 0 && ~operand2 + 1> 0) ||
                                          (alu_result > 0 && rf_d1_df < 0 && ~operand2 + 1 < 0) ? 1 : 0);
                      end
          opcode_cmpn: begin
                        alu_result = rf_d1_df + operand2;
                        if (de_pipe[20] == 1'b1 && rf_ws != 4'b1111)
                          cpsr[cpsr_v] = ((alu_result < 0 && rf_d1_df > 0 && operand2 > 0) ||
                                          (alu_result > 0 && rf_d1_df < 0 && operand2 < 0) ? 1 : 0);
                      end
          opcode_orr: alu_result = rf_d1_df | operand2;
          opcode_mov: alu_result = operand2;
          opcode_bic: alu_result = rf_d1_df & ~operand2;
          opcode_mvn: alu_result = 32'hFFFF_FFFF ^ operand2;
        endcase

        // Updates condition bits
        if (de_pipe[20] == 1'b1 && rf_ws != 4'b1111) begin
          cpsr[cpsr_c] = alu_result[32];
          cpsr[cpsr_z] = (alu_result == 33'h0_0000_0000 ? 1 : 0);
          cpsr[cpsr_n] = alu_result[31];
        end
      end

      if (inst_opcode(de_pipe) != opcode_tst &&
          inst_opcode(de_pipe) != opcode_teq &&
          inst_opcode(de_pipe) != opcode_cmp &&
          inst_opcode(de_pipe) != opcode_cmpn ||
          inst_branch_islink(de_pipe) == 1'b1)
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
    //if (~de_invalid) begin
      if (!nreset)
          pc <= 32'd0;
      else begin
        // default behavior
        if (pc > 65) begin
         pc <= 32'd0;
        end else begin
          pc <= pc + 4;
        end
        if (inst_type(de_pipe) == inst_type_branch || de_pipe[27:4] == branchExchange_opcode) begin
          case (inst_cond(de_pipe))
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
      //end
    end
  end

  always @(negedge clk) begin
    if (~de_invalid) begin
      if (inst_type(de_pipe) == inst_type_branch || de_pipe[27:4] == branchExchange_opcode) begin
          case (inst_cond(de_pipe))
            cond_eq: if (cpsr[cpsr_z] == 1'b1) begin
                fd_invalid <= 1'b1;
                de_invalid <= 1'b1;
              end
            cond_ne: if (~cpsr[cpsr_z]) begin
                fd_invalid <= 1'b1;
                de_invalid <= 1'b1;
              end
            cond_cs: if (cpsr[cpsr_c]) begin
                fd_invalid <= 1'b1;
                de_invalid <= 1'b1;
              end
            cond_cc: if (~cpsr[cpsr_c]) begin
                fd_invalid <= 1'b1;
                de_invalid <= 1'b1;
              end
            cond_ns: if (cpsr[cpsr_n]) begin
                fd_invalid <= 1'b1;
                de_invalid <= 1'b1;
              end
            cond_nc: if (~cpsr[cpsr_n]) begin
                fd_invalid <= 1'b1;
                de_invalid <= 1'b1;
              end
            cond_vs: if (cpsr[cpsr_v]) begin
                fd_invalid <= 1'b1;
                de_invalid <= 1'b1;
              end
            cond_vc: if (~cpsr[cpsr_v]) begin
                fd_invalid <= 1'b1;
                de_invalid <= 1'b1;
              end
            cond_hi: if (cpsr[cpsr_c] && ~cpsr[cpsr_z]) begin
                fd_invalid <= 1'b1;
                de_invalid <= 1'b1;
              end
            cond_ls: if (~cpsr[cpsr_c] || cpsr[cpsr_z]) begin
                fd_invalid <= 1'b1;
                de_invalid <= 1'b1;
              end
            cond_ge: if (cpsr[cpsr_n] == cpsr[cpsr_v]) begin
                fd_invalid <= 1'b1;
                de_invalid <= 1'b1;
              end
            cond_lt: if (cpsr[cpsr_n] != cpsr[cpsr_v]) begin
                fd_invalid <= 1'b1;
                de_invalid <= 1'b1;
              end
            cond_gt: if (~cpsr[cpsr_z] && cpsr[cpsr_n] == cpsr[cpsr_v]) begin
                fd_invalid <= 1'b1;
                de_invalid <= 1'b1;
              end
            cond_le: if (cpsr[cpsr_z] || cpsr[cpsr_n] != cpsr[cpsr_v]) begin
                fd_invalid <= 1'b1;
                de_invalid <= 1'b1;
              end
            cond_al: begin
                fd_invalid <= 1'b1;
                de_invalid <= 1'b1;
              end
            default: begin
              de_invalid <= fd_invalid;
              fd_invalid <= 1'b0;
            end
          endcase
            // pc <= branch_target; marks comment
        end
        else begin
          de_invalid <= fd_invalid;
          fd_invalid <= 1'b0;
        end
      end
      else begin
        de_invalid <= fd_invalid;
        fd_invalid <= 1'b0;
      end

  end

  always @(posedge clk) begin
    em_pipe <= de_pipe;
    em_invalid <= de_invalid;
    em_rf_we <= rf_we;
    em_rf_ws <= rf_ws;
    em_data_mem_we <= data_mem_we;
    // em_data_addr <= data_addr; COMMENTED THIS OUT to fix one cycle delay
    //em_data_mem_wd <= data_mem_wd;
  end

///////////////////////////////////////
// Memory

  always @(posedge clk) begin
    if (~em_invalid) begin
      if (em_data_mem_we)
          data_mem[data_addr] <= data_mem_wd;
      data_mem_rd <= data_mem[data_addr];
    end
  end




  always @(posedge clk) begin
    mwb_invalid <= em_invalid;
    //mwb_pipe <= em_pipe;
    mwb_rf_we <= em_rf_we;

    // I MADE CHANGES HERE. Idea is that we check if we load or store before writing
    if (inst_type(em_pipe) == inst_type_ldr_str && inst_ldrstr_isload(em_pipe) == inst_type_load)
      mwb_rf_wd <= data_mem_rd;
    else
      mwb_rf_wd <= rf_wd;



    mwb_rf_ws <= em_rf_ws;
  end

///////////////////////////////////////
// Write back

  // "Write back" the instruction
  always @(posedge clk) begin
    if (~mwb_invalid) begin
      if (nreset && mwb_rf_we)
        if (mwb_rf_ws != r15) // Also writes from data mem to register
          rf[mwb_rf_ws] <= mwb_rf_wd;
    end
  end
endmodule
