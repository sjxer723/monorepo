module sc_datamem (
	input resetn,
	input 			we,
	input 			clock,
	input			mem_clk,
	input [31:0] addr,
	input [31:0] datain,
	input [31:0] in_port0,
	input [31:0] in_port1,

	output	wire dmem_clk,
	output	wire [31:0] dataout,
	output	wire [31:0] out_port0,
	output	wire [31:0] out_port1,
	output 	wire [31:0] out_port2
);
	wire        	write_enable;
	wire [31:0]		mem_dataout; 
	wire [31:0]		io_read_data;
	wire 			write_data_enable;
	wire 			write_io_enable;
	
	assign	write_enable = we & ~clock; 
	assign	dmem_clk = mem_clk & ( ~ clock);
	
	//address 100000- 111111: I/O, 000000 -011111: data		
	assign	write_data_enable = write_enable &(~addr[7]);		
	assign	write_io_enable = write_enable & addr[7];
	
	//mux: choose whether mem or i/o
	mux2x32 io_data_mux(mem_dataout,io_read_data,addr[7],dataout);
	
	lpm_ram_dq_dram  dram(addr[6:2],dmem_clk,datain,write_data_enable,mem_dataout);
	
	io_output io_output_reg(
      .addr(addr), 
      .datain(datain), 
      .write_io_enable(write_io_enable), 
      .io_clk(dmem_clk), 
      .out_port0(out_port0), 
      .out_port1(out_port1), 
      .out_port2(out_port2)
   	);
   
	io_input io_input_reg(
      .addr(addr), 
      .io_clk(dmem_clk), 
      .io_read_data(io_read_data), 
      .in_port0(in_port0), 
      .in_port1(in_port1)
   	);
endmodule 