module out_port_seg(
	input [31:0] datain,
	output [6:0] led_ten,
	output [6:0] led_mod
);
	
	reg [3:0] res_ten, res_mod;
	always @(datain) begin
		res_ten = datain / 10;
		res_mod = datain % 10;
	end
	
	seven_seg led1(
		.bcd_in(res_ten),
		.seven_seg_out(led_ten)
	);
	
	seven_seg led2(
		.bcd_in(res_mod),
		.seven_seg_out(led_mod)
	);
	
	
endmodule 