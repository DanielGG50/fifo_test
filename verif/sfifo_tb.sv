class random_gen;
	rand bit [DATA_WIDTH-1:0] data;
	constraint data_range { data >= 0 && data < 2**DATA_WIDTH; }
endclass

class random_gen_lower_half_range extends random_gen;
	constraint data_range { data >= 0 && data < 2**(DATA_WIDTH-1); }
endclass

class random_gen_upper_half_range extends random_gen;
	constraint data_range { data >= 2**(DATA_WIDTH-1) && data < 2**DATA_WIDTH; }
endclass

module sfifo_tb;

	logic clk;
	logic arst_n;

	logic [DATA_WIDTH-1:0] q_verif [$];
	logic [DATA_WIDTH-1:0] data_out;
	logic [DATA_WIDTH-1:0] expected;

	

	initial clk = 0;
	always #5ns clk = ~clk;

	initial begin
		arst_n = 0;
		#20ns;
		arst_n = 1;
	end

	sfifo_intf if_i (
	  .clk(clk),
		.arst_n(arst_n)
	);


`ifdef TEST1

	random_gen_lower_half_range rg_lower;
	initial begin

		wait(arst_n == 1'b1);
		rg_lower = new();
		if_i.initialize();

		repeat (10) begin
			@(posedge clk);
			rg_lower.randomize();
			if_i.buffer_wr_data(rg_lower.data);
		end
		repeat (1000000) begin
			rg_lower.randomize();
			if_i.wr_or_rd_random(rg_lower.data);
		end	
	end
`endif

`ifdef TEST2

	random_gen_upper_half_range rg_upper;
	initial begin

		wait(arst_n == 1'b1);
		rg_upper = new();
		if_i.initialize();

		repeat (10) begin
			@(posedge clk);
			rg_upper.randomize();
			if_i.buffer_wr_data(rg_upper.data);
		end
		repeat (1000000) begin
			rg_upper.randomize();
			if_i.wr_or_rd_random(rg_upper.data);
		end	
	end
`endif


	always_ff @(posedge clk) begin
		if (if_i.rden && !if_i.empty) begin
			data_out <= if_i.rdata;
			expected <= q_verif.pop_front();
		end
		if (if_i.wren && !if_i.full) begin
			q_verif.push_back(if_i.wdata);
		end
	end

	check_data_out: assert property (@(posedge clk) disable iff (!arst_n) (if_i.rden && !if_i.empty) |=> (data_out === expected))
	else $error("Data Mismatch: expected %0h, got %0h", expected, data_out);



	initial begin
		#1ms $finish;
	end

	initial begin
	  $shm_open("shm_db");
	  $shm_probe("ASMTR");

	end	

  sfifo sfifo_i (
  .clk(if_i.clk),
	.arst_n(if_i.arst_n),
	// Writing port //
	.wren(if_i.wren),
	.wdata(if_i.wdata),
	.pre_full(if_i.pre_full),
	.full(if_i.full),
	// Reading port //
	.rden(if_i.rden),
	.rdata(if_i.rdata),
	.pre_empty(if_i.pre_empty),
	.empty(if_i.empty)
  );

bind sfifo fv_sfifo fv_sfifo_i (.*);
bind sfifo cov_sfifo sfifo_cov_i (.*); 

endmodule
