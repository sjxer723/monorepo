module sc_cu (op, func, z, wmem, wreg, regrt, m2reg, aluc, shift,
              aluimm, pcsource, jal, sext);
   input  [5:0] op,func;
   input        z;
   output       wreg,regrt,jal,m2reg,shift,aluimm,sext,wmem;
   output [3:0] aluc;
   output [1:0] pcsource;
   wire r_type = ~|op;
	

	/*
	* Step1: Instruction decode
	**/
   wire i_add = r_type && (func == 6'h20);	//100000
   wire i_sub = r_type && (func == 6'h22);	//100010
   wire i_and = r_type && (func == 6'h24);	//100100
   wire i_or  = r_type && (func == 6'h25);	//100101
   wire i_xor = r_type && (func == 6'h26);	//100110 
   wire i_sll = r_type && (func == 6'h00);	//000000
   wire i_srl = r_type && (func == 6'h02);	//000010
   wire i_sra = r_type && (func == 6'h03);	//000011
   wire i_jr  = r_type && (func == 6'h08);	//001000
	wire i_cont =r_type && (func == 6'h09);	//001001
                
   wire i_addi = (op == 6'b001000);	//001000
   wire i_andi = (op == 6'b001100);	//001100   
   wire i_ori  = (op == 6'b001101);	//001101
   wire i_xori = (op == 6'b001110); //001110 
   wire i_lw   = (op == 6'b100011);	//100011
   wire i_sw   = (op == 6'b101011);	//101011
   wire i_beq  = (op == 6'b000100);	//000100
   wire i_bne  = (op == 6'b000101); //000101
   wire i_lui  = (op == 6'b001111); //001111
   wire i_j    = (op == 6'b000010); //000010
   wire i_jal  = (op == 6'b000011); //000011


   assign pcsource[1] = i_jr | i_j | i_jal;
   assign pcsource[0] = ( i_beq & z ) | (i_bne & ~z) | i_j | i_jal ;

   assign wreg = i_add | i_sub | i_and | i_or   | i_xor  |
                 i_sll | i_srl | i_sra | i_addi | i_andi |
                 i_ori | i_xori | i_lw | i_lui  | i_jal  | i_cont;

   assign aluc[3] = i_sra | i_cont;
   assign aluc[2] = i_sub | i_or   | i_lui | i_srl | i_sra | i_ori;		//ori
   assign aluc[1] = i_xor | i_xori | i_bne | i_beq | i_lui | i_sll | i_srl | i_sra | i_cont;
   assign aluc[0] = i_and | i_andi | i_or  | i_ori | i_sll | i_srl | i_sra | i_cont;

	assign shift   = i_sll | i_srl  | i_sra ;
	
	//aluimm =1: 使用imm 0: 不使用imm

   assign aluimm  = i_addi| i_andi | i_ori | i_xori | i_lui | i_lw | i_sw;
	

	//sext = 1: 做符号位扩展 0: 不做符号位扩展
	assign sext    = i_addi| i_lw | i_beq | i_bne | i_sw;		//sw
	
	//wmem = 1: 写入内存 0: 不写入内存

   assign wmem    = i_sw;

	//m2reg =1: 从内存中取数写入寄存器
	assign m2reg   = i_lw;
	
	//regrt = 1: 选择rt作为目标写入寄存器 0: 选择rd作为目标写入寄存器

   assign regrt   = i_addi | i_andi | i_ori | i_xori | i_lw | i_lui;

	assign jal     = i_jal;

endmodule

