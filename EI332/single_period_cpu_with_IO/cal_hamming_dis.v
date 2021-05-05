module cal_hamming_dis(
	input [31:0] src1,
	input [31:0] src2,
	output reg [31:0] res
	);
	
	integer i;
	always @(*) begin
		for(i=0; i<32;i=i+1)
			res = res+src1[i] ^src2[i];
	end
	
endmodule	