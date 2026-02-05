interface sfifo_intf (
  input logic clk,
  input logic arst_n
);

  // Writing port //
	logic wren;
	logic [DATA_WIDTH-1:0] wdata;
	logic pre_full;
	logic full;
	// Reading port //
	logic rden;
	logic [DATA_WIDTH-1:0] rdata;
	logic pre_empty;
	logic empty;

  task automatic initialize();
  	rden = 1'b0;
    wren = 1'b0;
    repeat (1) @(posedge clk);
  endtask

  task automatic buffer_wr_data(logic [DATA_WIDTH-1:0] data);
    if(!(full || pre_full)) begin
      wren <= 1'b1;
      wdata <= data;
      repeat (1) @(posedge clk);
      wren <= 1'b0;
    end
  endtask

	task automatic buffer_rd_data();
    if(!(empty || pre_empty)) begin
		  rden <= 1'b1;
		  repeat (1) @(posedge clk);
		  rden <= 1'b0;
    end
	endtask

	task automatic wr_or_rd_random(input logic [DATA_WIDTH-1:0] random_data);
		if($urandom_range(0,1) == 1) begin
			buffer_wr_data(random_data);
		end else begin
			buffer_rd_data();
		end
	endtask

endinterface
