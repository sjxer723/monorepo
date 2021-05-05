module in_port(
    input sw0, 
    input sw1, 
    input sw2, 
    input sw3, 
    input sw4,
    output wire [31: 0] res
);

    assign res[0] = sw0;
    assign res[1] = sw1;
    assign res[2] = sw2;
    assign res[3] = sw3;
    assign res[4] = sw4;
    assign res[31: 5] = 27'b0;

endmodule