module fv_sfifo #(parameter DATA_WIDTH = 32, parameter NUM_ELEMENTS = 64) (
	input logic clk,
	input logic arst_n,
	// Writing port //
	input logic wren,
	input logic [DATA_WIDTH-1:0] wdata,
	input logic pre_full,
	input logic full,
	// Reading port //
	input logic rden,
	input logic [DATA_WIDTH-1:0] rdata,
	input logic pre_empty,
	input logic empty
);

  // When fifo is full, a write should not happen
  no_wren_when_full: assert property (@(posedge clk) full |-> wren == 1'b0);

  // When fifo is empty, a read should not happen
  no_rden_when_empty: assert property (@(posedge clk) empty |-> rden == 1'b0);

  // fifo can not be full and empty at the same time
  no_full_and_empty: assert property (@(posedge clk) 1'b1 |-> ~(full && empty) );

endmodule: fv_sfifo
