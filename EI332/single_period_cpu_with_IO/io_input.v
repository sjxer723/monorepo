module io_input(
	input  [31:0] addr,
	input			 io_clk,
	input	 [31:0] in_port0,
	input	 [31:0] in_port1,
	output [31:0] io_read_data
);
	
	reg [31:0] in_reg0;
	reg [31:0] in_reg1;
	
	io_input_mux io_input_mux2x32(in_reg0,in_reg1,addr[7:2],io_read_data);
	
	always @(posedge io_clk) begin
		in_reg0 <= in_port0;
		in_reg1 <= in_port1;
	end
endmodule
