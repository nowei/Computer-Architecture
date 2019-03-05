module mem_pre_decode(
    input   [31:0]  inst,
    input           cond_go,
    input   [31:0]  adder_result,
    input   [31:0]  base_reg,  
    input   [31:0]  rf_data,
    output  reg [31:0]  mem_addr,
    output  reg [31:0]  mem_write_data,
    output  reg [3:0]   mem_write_enable,
    output  reg     mem_read_enable,
    output  reg     is_mmio
    );
  `include "arm32_base.v"

  always @(*) begin
    mem_addr = adder_result;
    if (inst_sdt_pre(inst) == sdt_is_post)
      mem_addr = base_reg;

    if ((mem_addr & mmio_mask) == mmio_mask)
      is_mmio = true;
    else
      is_mmio = false;

    mem_write_enable = 4'b0000;
    mem_write_data = 32'd0;

    if (inst_sdt_byte(inst) == sdt_is_byte) begin
      mem_write_data[7:0] = rf_data[7:0];
      mem_write_data[15:8] = rf_data[7:0];
      mem_write_data[23:16] = rf_data[7:0];
      mem_write_data[31:24] = rf_data[7:0];
    end else begin
      if (endian == little_endian) begin
        mem_write_data[7:0] = rf_data[7:0];
        mem_write_data[15:8] = rf_data[15:8];
        mem_write_data[23:16] = rf_data[23:16];
        mem_write_data[31:24] = rf_data[31:24];
      end else begin
        mem_write_data[31:24] = rf_data[7:0];
        mem_write_data[23:16] = rf_data[15:8];
        mem_write_data[15:8] = rf_data[23:16];
        mem_write_data[7:0] = rf_data[31:24];
      end
    end

    if(inst_type(inst) == inst_type_sdt &&
       inst_sdt_load(inst) == sdt_is_store &&
       cond_go &&
       !is_mmio) begin
      if (inst_sdt_byte(inst) == sdt_is_byte) begin
        case (mem_addr[1:0])
          2'b00:  mem_write_enable[0] = true;
          2'b01:  mem_write_enable[1] = true;
          2'b10:  mem_write_enable[2] = true;
          2'b11:  mem_write_enable[3] = true;
        endcase
      end else begin
        mem_write_enable[3:0] = 4'b1111;
      end
    end

    if (inst_type(inst) == inst_type_sdt &&
        inst_sdt_load(inst) == sdt_is_load 
        && cond_go && !is_mmio)
      mem_read_enable = true;
    else
      mem_read_enable = false;
  end

endmodule