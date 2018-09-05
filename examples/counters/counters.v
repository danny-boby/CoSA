module Counters #(parameter SIZE = 10) (input clk, output [SIZE-1:0] q);

   reg [SIZE-1:0] val1;
   reg [SIZE-1:0] val2;
   
   
   Counter #(.SIZE(SIZE)) counter1  (.clk (clk),
	             .val (val1));

   Counter #(.SIZE(SIZE)) counter2 (.clk (clk),
	             .val (val2));

   assign q = val1 + val2;
   
     
endmodule

module Counter #(parameter SIZE = 16) (input clk, output [SIZE-1:0] val);

   always @(posedge clk) begin
       val <= val + 1;
   end

endmodule
