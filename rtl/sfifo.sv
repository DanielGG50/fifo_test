module sfifo (
	input logic clk,
	input logic arst_n,
	// Writing port //
	input logic wren,
	input logic [DATA_WIDTH-1:0] wdata,
	output logic pre_full,
	output logic full,
	// Reading port //
	input logic rden,
	output logic [DATA_WIDTH-1:0] rdata,
	output logic pre_empty,
	output logic empty
);

  localparam ADDR_WIDTH = $clog2(NUM_ELEMENTS);
  
  logic [DATA_WIDTH-1:0] mem [NUM_ELEMENTS];
  logic [ADDR_WIDTH-1:0] wrptr;
  logic [ADDR_WIDTH-1:0] rdptr;
  logic [ADDR_WIDTH-1:0] next_wrptr;
  logic [ADDR_WIDTH-1:0] next_rdptr;

  always_ff@(posedge clk, negedge arst_n) begin
    if(~arst_n) begin
      empty <= 1'b1;
    end else begin
      if(wren && (~rden)) begin
        empty <= 1'b0;
      end else if(pre_empty) begin
        empty <= 1'b1;
      end
    end
  end
  
  always_ff@(posedge clk, negedge arst_n) begin
    if(~arst_n) begin
      full <= 1'b0;
    end else begin
      if(rden && (~wren)) begin
        full <= 1'b0;
      end else if(pre_full) begin
        full <= 1'b1;
      end
    end
  end

  always_ff@(posedge clk, negedge arst_n) begin
    if(~arst_n) begin
      wrptr <= 'd0;
    end else begin
      if(wren && (~full)) begin
        wrptr <= next_wrptr;
      end
    end
  end
  
  always_ff@(posedge clk, negedge arst_n) begin
    if(~arst_n) begin
      rdptr <= 'd0;
    end else begin
      if(rden && (~empty)) begin
        rdptr <= next_rdptr;
      end
    end
  end
  
  always_ff@(posedge clk) begin
    if(wren && (~full)) begin
      mem[wrptr] <= wdata;
    end
  end
  
  assign next_wrptr = wrptr + 1'b1;
  assign next_rdptr = rdptr + 1'b1;
  assign pre_empty = (next_rdptr == wrptr) && rden && (~wren);
  assign pre_full = (next_wrptr == rdptr) && wren && (~rden);
  assign rdata = mem[rdptr];

endmodule: sfifo
