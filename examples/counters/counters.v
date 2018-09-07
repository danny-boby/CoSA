module Counters #(parameter SIZE = 10) 
   (
    input             clk, 
    input             rst, 
    output [SIZE-1:0] out
    );

   reg [SIZE-1:0] val1;
   reg [SIZE-1:0] val2;
   
   Counter #(.SIZE(SIZE)) counter1 (.clk (clk), .rst (rst), .val (val1));
   Counter #(.SIZE(SIZE)) counter2 (.clk (clk), .rst (rst), .val (val2));
   Adder #(.SIZE(SIZE)) adder (.in1 (val1), .in2 (val2), .out (out));

endmodule

module Counter #(parameter SIZE = 16) 
   (
    input             clk,
    input             rst,
    output [SIZE-1:0] val
    );

   initial val = 'b0;
   
   always @(posedge clk or posedge rst)
     begin
        if (rst)
          val = 'b0;
        else
          val <= val + 1;
     end

endmodule

module Adder #(parameter SIZE = 16) 
   (
    input [SIZE-1:0]  in1, 
    input [SIZE-1:0]  in2, 
    output [SIZE-1:0] out
    );

   assign out = in1 + in2;
   
endmodule
