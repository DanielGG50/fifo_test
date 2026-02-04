module sfifo_tb;

  parameter DATA_WIDTH = 32;
  parameter NUM_ELEMENTS = 16; 

	logic clk;
	logic arst_n;
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

	initial clk = 0;
	always #5ns clk = ~clk;

	initial begin
		arst_n = 0;
		#50ns;
		arst_n = 1;
	end


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

	initial begin
		rden <= 1'b0;
    wren <= 1'b0;
		repeat (10) begin
			@(posedge clk);
			buffer_wr_data($urandom_range(0, 2**DATA_WIDTH-1));
		end
		repeat (1000000) begin
			@(posedge clk);
			std::randomize(wdata);
			wr_or_rd_random(wdata);
		end	
	end


	initial begin
		#1ms $finish;
	end

	initial begin
	  $shm_open("shm_db");
	  $shm_probe("ASMTR");

	end	

  sfifo #(.DATA_WIDTH(DATA_WIDTH), .NUM_ELEMENTS(NUM_ELEMENTS)) sfifo_i (
  .clk(clk),
	.arst_n(arst_n),
	// Writing port //
	.wren(wren),
	.wdata(wdata),
	.pre_full(pre_full),
	.full(full),
	// Reading port //
	.rden(rden),
	.rdata(rdata),
	.pre_empty(pre_empty),
	.empty(empty)
  );

bind sfifo fv_sfifo #(DATA_WIDTH, NUM_ELEMENTS) fv_sfifo_i (.*);

endmodule
