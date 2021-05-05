//2-way 32 bits multiplexers

module mux2x32 (
    input [31: 0] a0,
    input [31: 0] a1,
    input sel,
    output wire [31: 0] y
);
    
   
    assign y = (sel ? a1 : a0);
   
endmodule