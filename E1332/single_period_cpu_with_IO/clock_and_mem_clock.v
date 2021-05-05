module clock_and_mem_clock(
	input main_clk,
	output reg clock_out,
	output mem_clk
	);
	
	assign mem_clk = main_clk;
	
	initial begin
        clock_out <= 1'b0;
   end
	
	always @(posedge main_clk) begin
		clock_out <=!clock_out;
	end

endmodule

	