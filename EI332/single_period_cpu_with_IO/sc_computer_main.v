/////////////////////////////////////////////////////////////
//                                                         //
// School of Software of SJTU                              //
//                                                         //
/////////////////////////////////////////////////////////////

module sc_computer_main (
	resetn,clock,mem_clk,
	in_port0,in_port1,
	pc,inst,aluout,memout,
	imem_clk,dmem_clk,
	out_port0,out_port1,out_port2
	);
   
	input resetn,clock,mem_clk;
	input  [31:0] in_port0,in_port1;
	output [31:0] pc,inst,aluout,memout;
   output        imem_clk,dmem_clk;
	output [31:0] out_port0,out_port1,out_port2;
	
	// all these "wire"s are used to connect or interface the cpu,dmem,imem and so on.
	wire   [31:0] data;
	wire          wmem;
	wire 	 [31:0] mem_dataout,io_read_data;
	
	sc_cpu	cpu(clock, resetn, inst, memout, pc, wmem, aluout, data); 
   
	sc_instmem imem(
        .addr(pc), 
        .clock(clock), 
        .mem_clk(mem_clk), 
        .inst(inst), 
        .imem_clk(imem_clk)
    ); 

    sc_datamem dmem(
        .resetn(resetn),
        .we(wmem), 
        .clock(clock), 
        .mem_clk(mem_clk),  
        .addr(aluout), 
        .datain(data), 
        .in_port0(in_port0), 
        .in_port1(in_port1), 

        .dmem_clk(dmem_clk), 
        .dataout(memout), 
        .out_port0(out_port0), 
        .out_port1(out_port1), 
        .out_port2(out_port2)
    ); 
endmodule



