module sc_computer(
	input SW0,
	input SW1,
	input SW2,
	input SW3,
	input SW4,
	input SW5,
	input SW6,
	input SW7,
	input SW8,
	input SW9,
	input clk,
	input resetn,
	
	output [6:0] HEX0,
	output [6:0] HEX1,
	output [6:0] HEX2,
	output [6:0] HEX3,
	output [6:0] HEX4,
	output [6:0] HEX5
);

	wire  clock_out,mem_clk,imem_clk,dmem_clk;
	wire  [31:0] in_port0,in_port1;
    wire  [31:0] pc,inst,aluout,memout;
	wire  [31:0] out_port0,out_port1,out_port2;
	
	in_port inst1 (SW0,SW1,SW2,SW3,SW4,in_port0);
	in_port inst2 (SW5,SW6,SW7,SW8,SW9,in_port1);
	
	clock_and_mem_clock inst3(
		.main_clk(clk),.clock_out(clock_out),.mem_clk(mem_clk)
	);
	
	sc_computer_main inst4(
		.resetn(resetn),
		.clock(clock_out),
		.mem_clk(mem_clk),
		.in_port0(in_port0),
		.in_port1(in_port1),
		.pc(pc),
		.inst(inst),
		.aluout(aluout),
		.memout(memout),
		.imem_clk(imem_clk),
		.dmem_clk(dmem_clk),
		.out_port0(out_port0),
		.out_port1(out_port1),
		.out_port2(out_port2)
	);
	
	out_port_seg  inst5(out_port0, HEX1,HEX0);
	out_port_seg  inst6(out_port1, HEX3,HEX2);
	out_port_seg  inst7(out_port2, HEX5,HEX4);
endmodule