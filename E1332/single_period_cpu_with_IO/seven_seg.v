module seven_seg(
	input [3:0] bcd_in,
	output reg [6:0] seven_seg_out
);
	always @(*) begin
		case (bcd_in)
			0: seven_seg_out <= 7'b1111110;
			1: seven_seg_out <= 7'b0110000;
			2: seven_seg_out <= 7'b1101101;
			3: seven_seg_out <= 7'b1111001;
			4: seven_seg_out <= 7'b0110011;
			5: seven_seg_out <= 7'b1011011;
			6: seven_seg_out <= 7'b1011111;
			7: seven_seg_out <= 7'b1110000;
			8: seven_seg_out <= 7'b1111111;
			9: seven_seg_out <= 7'b1111011;
			default: seven_seg_out <= 0;
		endcase
	end
endmodule