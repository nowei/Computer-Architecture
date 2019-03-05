module mem(
    input   clk,
    input   do_read,
    input   [31:0]  mem_addr,
    input   [3:0]   do_write_byte,
    input   [31:0]  mem_write_data,
    output  reg [31:0]  mem_read_data
    );

`include "arm32_base.v"

// Data memory
  reg [7:0]   data0[0:data_words - 1];
  reg [7:0]   data1[0:data_words - 1];
  reg [7:0]   data2[0:data_words - 1];
  reg [7:0]   data3[0:data_words - 1];
  initial begin
    // Mirror code into data segment
    $readmemh("testcode/code_data0.hex", data0, 0);
    $readmemh("testcode/code_data1.hex", data1, 0);
    $readmemh("testcode/code_data2.hex", data2, 0);
    $readmemh("testcode/code_data3.hex", data3, 0);

    // Put the actual data up by 4096 bytes (1024 X 4)
    $readmemh("testcode/data0.hex", data0, 1024);
    $readmemh("testcode/data1.hex", data1, 1024);
    $readmemh("testcode/data2.hex", data2, 1024);
    $readmemh("testcode/data3.hex", data3, 1024);
  end

  always @(posedge clk) begin
    if (do_read) begin
      mem_read_data[7:0] <= data0[mem_addr[data_addr_width - 1:2]];
      mem_read_data[15:8] <= data1[mem_addr[data_addr_width - 1:2]];
      mem_read_data[23:16] <= data2[mem_addr[data_addr_width - 1:2]];
      mem_read_data[31:24] <= data3[mem_addr[data_addr_width - 1:2]];
    end
    if (do_write_byte[0])
      data0[mem_addr[data_addr_width - 1:2]] <= mem_write_data[7:0];
    if (do_write_byte[1])
      data1[mem_addr[data_addr_width - 1:2]] <= mem_write_data[15:8];
    if (do_write_byte[2])
      data2[mem_addr[data_addr_width - 1:2]] <= mem_write_data[23:16];
    if (do_write_byte[3])
      data3[mem_addr[data_addr_width - 1:2]] <= mem_write_data[31:24];
  end

endmodule