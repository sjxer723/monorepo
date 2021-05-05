module cla32 (pc,x1,x2,p4);
   input [31:0] pc;
   input [31:0] x1,x2;
   
   output [31:0] p4;
   
   assign p4 = pc + x1;//32'h4;   
 //  assign adr = p4 + offset;
   
endmodule 
