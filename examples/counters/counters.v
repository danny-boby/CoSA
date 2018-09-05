module test (input clk, output [7:0] q);

   reg [7:0] val1;
   reg [7:0] val2;
   
   
   Counter counter1 (.clk (clk),
	             .val (val1));

   Counter counter2 (.clk (clk),
	             .val (val2));

   assign q = val1 + val2;
   
     
endmodule

module Counter (input clk, output [7:0] val);

   always @(posedge clk) begin
       val <= val + 1;
   end

endmodule
