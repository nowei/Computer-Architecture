module cpu(
  input wire clk,
  input wire nreset,
  output wire led,
  output wire [7:0] debug_port1,
  output wire [7:0] debug_port2,
  output wire [7:0] debug_port3,
  output wire [7:0] debug_port4,
  output wire [7:0] debug_port5,
  output wire [7:0] debug_port6,
  output wire [7:0] debug_port7
  );

`include "arm32_base.v"

  // Debug outputs
  assign led = led_debug;
  assign debug_port1 = pc[7:0];
  assign debug_port2 = {zero, last_phase, zero, phase };
  assign debug_port3 = program_debug;
  assign debug_port4 = debug_word[31:24];
  assign debug_port5 = debug_word[23:16];
  assign debug_port6 = debug_word[15:8];
  assign debug_port7 = debug_word[7:0];

  reg [31:0] debug_word;
  always @(*) begin
    case (phase)
      phase_fetch:      debug_word = pc;
      phase_regread:    debug_word = inst;
      phase_mem:        debug_word = alu_result[31:0];
      phase_regwrite1:  debug_word = { rf_ws1, 3'b000, rf_we1, rf_wd1[23:0] };
      phase_regwrite2:  debug_word = rf_d1;
      3'b101:           debug_word = mem_addr;
      3'b110:           debug_word = { mem_we, 3'b000, mem_re, mem_write_data[23:0] };
      phase_fault:      debug_word = mem_load_data;
      default:          debug_word = 32'd0;
    endcase
  end

  // one byte of output to send to the debugger programmically.  This is a register.
  reg [7:0] program_debug;

  // LED we also expose to the program for setting.
  reg       led_debug;

  // This is a multi-cycle execution engine.  These are the phases.
  localparam phase_fetch = 3'b000;
  localparam phase_regread = 3'b001;
  localparam phase_mem = 3'b010;
  localparam phase_regwrite1 = 3'b011;
  localparam phase_regwrite2 = 3'b100;
  localparam phase_fault = 3'b111;
  reg [2:0] phase;

//  "Fetch" from code memory into instruction bits 
  reg [31:0]  pc;
  wire [31:0] inst;
  fetch the_instruction_memory( .clk(clk),
                                .do_fetch(phase == phase_fetch),
                                .pc(pc),
                                .inst(inst));

  wire [31:0] pc_plus4;
  wire [31:0] pc_plus8;
  wire [31:0] pc_plus12;
  pc_logic the_pc_logic(.clk(clk),
                        .nreset(nreset),
                        .inst(inst),
                        .rf_d2(rf_d2),
                        .rf_we1(rf_we1),
                        .rf_ws1(rf_ws1),
                        .rf_wd1(rf_wd1),
                        .rf_we2(rf_we2),
                        .rf_ws2(rf_ws2),
                        .rf_wd2(rf_wd2),
                        .cond_go(cond_go),
                        .do_update(phase == last_phase),
                        .pc(pc),
                        .pc_plus4(pc_plus4),
                        .pc_plus8(pc_plus8),
                        .pc_plus12(pc_plus12));

  // Decode what gets read and written from the register file
  wire [3:0] rf_rs1;
  wire [3:0] rf_rs2;
  wire [3:0] rf_rs3;
  wire [3:0] rf_ws1;
  wire [3:0] rf_ws2;
  wire rf_we1;
  wire rf_we2;
  reg_decode the_reg_decode(.inst(inst),
                            .cond_go(cond_go),
                            .rf_rs1(rf_rs1),
                            .rf_rs2(rf_rs2),
                            .rf_rs3(rf_rs3),
                            .rf_ws1(rf_ws1),
                            .rf_ws2(rf_ws2),
                            .rf_we1(rf_we1),
                            .rf_we2(rf_we2));

  // The actual register file proper
  wire [31:0] rf_d1_raw;
  wire [31:0] rf_d2_raw;
  wire [31:0] rf_d3_raw;
  reg [31:0] rf_wd1;
  reg [31:0] rf_wd2;
  reg_file the_reg_file(.clk(clk),
                        .rf_rs1(rf_rs1),
                        .rf_rs2(rf_rs2),
                        .rf_rs3(rf_rs3),
                        .rf_ws1(rf_ws1),
                        .rf_ws2(rf_ws2),
                        .rf_wd1(rf_wd1),
                        .rf_wd2(rf_wd2),
                        .rf_we1(rf_we1),
                        .rf_we2(rf_we2),
                        .next_cpsr(next_cpsr),
                        .set_cond_bits(set_cond_bits),
                        .do_read(phase == phase_regread),
                        .do_write1(phase == phase_regwrite1),
                        .do_write2(phase == phase_regwrite2),
                        .rf_d1(rf_d1_raw),
                        .rf_d2(rf_d2_raw),
                        .rf_d3(rf_d3_raw),
                        .cpsr(cpsr));

  // Patch the register file results with PC info as necessary
  wire [31:0] cpsr;
  reg [31:0] rf_d1;
  reg [31:0] rf_d2;
  reg [31:0] rf_d3;
  always @(*) begin
    rf_d1 = (rf_rs1 == r15) ?
      ((inst_type(inst) == inst_type_data_proc && shift_source(inst) == shift_reg) ? pc_plus12 : pc_plus8) : rf_d1_raw;
    rf_d2 = (rf_rs2 == r15) ?
      ((inst_type(inst) == inst_type_data_proc && shift_source(inst) == shift_reg) ? pc_plus12 : pc_plus8) : rf_d2_raw;
    rf_d3 = (rf_rs3 == r15) ?
      (((inst_type(inst) == inst_type_data_proc && shift_source(inst) == shift_reg) ||
       (inst_type(inst) == inst_type_sdt && inst_sdt_load(inst) == sdt_is_store)) ? pc_plus12 : pc_plus8) : rf_d3_raw;
  end  

  // Figure out what is written to the register file
  always @(*) begin
    rf_wd1 = (inst_type(inst) == inst_type_branch_and_link) ? pc_plus4 :
             (inst_type(inst) == inst_type_sdt && inst_sdt_load(inst) == sdt_is_load) ? (mem_load_data) :
             (inst_type(inst) == inst_type_data_proc) ? alu_result[31:0] : 
             32'b0;
    rf_wd2 = adder_result[31:0];
  end

  // Decode the condition in the instruction relative to the flags
  reg cond_go;
  reg set_cond_bits;
  flag_compute the_flag_compute(.inst(inst),
                                .cpsr(cpsr),
                                .cond_go(cond_go),
                                .set_cond_bits(set_cond_bits));

  reg [32:0] shifter_output;
  reg carry_from_shift;
  shifter the_shifter(.inst(inst),
                      .register_input(rf_d2),
                      .shift_register_input(rf_d3),
                      .in_cpsr_c(cpsr[cpsr_c]),
                      .shifter_output(shifter_output),
                      .carry_from_shift(carry_from_shift));


  reg [31:0]  next_cpsr;
  reg [32:0] alu_result;
  reg [32:0] adder_result;
  alu the_alu(.inst(inst),
              .operand1({ zero, rf_d1 }),
              .operand2(shifter_output),
              .cpsr(cpsr),
              .carry_from_shift(carry_from_shift),
              .result(alu_result),
              .next_cpsr(next_cpsr),
              .adder_result(adder_result));

  wire [31:0]   mem_addr;
  wire [31:0]   mem_write_data;
  wire [3:0]    mem_we;
  wire          mem_re;
  wire          is_mmio;
  mem_pre_decode  the_mem_pre_decode(
    .inst(inst),
    .cond_go(cond_go),
    .adder_result(adder_result[31:0]),
    .base_reg(rf_d1),
    .rf_data(rf_d3),
    .mem_addr(mem_addr),
    .mem_write_data(mem_write_data),
    .mem_write_enable(mem_we),
    .mem_read_enable(mem_re),
    .is_mmio(is_mmio));

  wire  [31:0]  mem_read_data;
  mem the_mem(
    .clk(clk),
    .mem_addr(mem_addr),
    .do_read(phase == phase_mem ? mem_re : false),
    .do_write_byte(phase == phase_mem ? mem_we : 4'd0),
    .mem_write_data(mem_write_data),
    .mem_read_data(mem_read_data));

  wire [31:0] mem_load_data;
  mem_post_decode the_mem_post_decode(
    .inst(inst),
    .mem_addr(mem_addr),
    .mem_read_data(mem_read_data),
    .mem_data_load(mem_load_data));

  // Determine what the last phase of execution will be.
  reg [2:0] last_phase;
  always @(*) begin
    if (phase == phase_fetch)
      last_phase = phase_regwrite2;
    else
      case (inst_type(inst))
        inst_type_data_proc:            last_phase = phase_regwrite1;
        inst_type_branch:               last_phase = phase_mem;
        inst_type_branch_and_link:      last_phase = phase_regwrite1;
        inst_type_branch_and_exchange:  last_phase = phase_mem;
        inst_type_sdt:
          if (inst_sdt_wb(inst) == sdt_is_base_write)
            last_phase = phase_regwrite2;
          else
          if (inst_sdt_load(inst) == sdt_is_load)
            last_phase = phase_regwrite1;
          else
            last_phase = phase_mem;
        inst_type_not_implemented:      last_phase = phase_fault;
        default:
          last_phase = phase_fault;
      endcase

    // Uncommenting this line is sometimes useful for debugging.  Puts more output to debug console.  
    //last_phase = phase_fault;
  end

  // It's possible to skip some phases (like mem access) for some instructions, but we don't.
  always @(posedge clk) begin
    if (!nreset)
      phase <= phase_fetch;
    else begin
      if (phase == last_phase)
        phase <= phase_fetch;
      else
        phase <= phase + 1;
    end
  end

  // I/O.  Well output for now at least.  This lets executed ARM code
  // talk to one of the debug Verilog ports.
  always @(posedge clk) begin
    if (phase == phase_mem &&
        inst_type(inst) == inst_type_sdt &&
        inst_sdt_load(inst) == sdt_is_store &&
        is_mmio &&
        cond_go) begin
      case (mem_addr[15:0])
        // Send the byte to the debugger
        16'h0000: program_debug <= mem_write_data[7:0];
        // Set the LED
        16'h0010: led_debug <= mem_write_data[0];
        default: begin end
      endcase
    end
  end
    
endmodule
