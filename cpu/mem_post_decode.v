module mem_post_decode(
    input   [31:0]  inst,
    input   [31:0]  mem_addr,
    input   [31:0]  mem_read_data,
    output  reg [31:0]  mem_data_load
    );

`include "arm32_base.v"

  always @(*) begin
    mem_data_load = 32'd0;
    if (inst_type(inst) == inst_type_sdt &&
        inst_sdt_load(inst) == sdt_is_load) begin
      if (inst_sdt_byte(inst) == sdt_is_byte)
        case (mem_addr[1:0])
          2'b00:  mem_data_load[7:0] = mem_read_data[7:0];
          2'b01:  mem_data_load[7:0] = mem_read_data[15:8];
          2'b10:  mem_data_load[7:0] = mem_read_data[23:16];
          2'b11:  mem_data_load[7:0] = mem_read_data[31:24];
        endcase
      else begin
        if (endian == little_endian)
          mem_data_load = { mem_read_data[31:24], mem_read_data[23:16], mem_read_data[15:8], mem_read_data[7:0] };
        else
          mem_data_load = { mem_read_data[7:0], mem_read_data[15:8], mem_read_data[23:16], mem_read_data[31:24] };
      end
    end
  end
endmodule

