module cov_sfifo (
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

  `define FIFO_PATH sfifo_i

  covergroup wr_port_cg @(posedge clk);
    option.per_instance = 1;
    
    wren_change: coverpoint wren {
    bins rise = (0 => 1);
    bins fall = (1 => 0);
    }
    wren_value: coverpoint wren { bins value[] = {0, 1}; }

    pre_full_change: coverpoint pre_full {
    bins rise = (0 => 1);
    bins fall = (1 => 0);
    }
    pre_full_value: coverpoint pre_full { bins value[] = {0, 1}; }

    full_change: coverpoint full {
    bins rise = (0 => 1);
    bins fall = (1 => 0);
    }
    full_value: coverpoint full { bins value[] = {0, 1}; }

    coverpoint wdata { bins wdata_dist[64] = {[0 : (1 << DATA_WIDTH) - 1]}; }

  endgroup: wr_port_cg



  covergroup rd_port_cg @(posedge clk);
    option.per_instance = 1;
    
    rden_change: coverpoint rden {
    bins rise = (0 => 1);
    bins fall = (1 => 0);
    }
    rden_value: coverpoint rden { bins value[] = {0, 1}; }

    pre_empty_change: coverpoint pre_empty {
    bins rise = (0 => 1);
    bins fall = (1 => 0);
    }
    pre_empty_value: coverpoint pre_empty { bins value[] = {0, 1}; }

    empty_change: coverpoint empty {
    bins rise = (0 => 1);
    bins fall = (1 => 0);
    }
    empty_value: coverpoint empty { bins value[] = {0, 1}; }

    coverpoint rdata { bins rdata_dist[64] = {[0 : (1 << DATA_WIDTH) - 1]}; }
  
  endgroup: rd_port_cg


  localparam ADDR_WIDTH = $clog2(NUM_ELEMENTS);

  covergroup ptrs_cg @(posedge clk);
    option.per_instance = 1;
  
    // Add pointer related coverage here if needed
    wrptr: coverpoint `FIFO_PATH.wrptr { bins wrptr_dist[] = {[0 : (1 << ADDR_WIDTH) - 1]}; }
    rdptr: coverpoint `FIFO_PATH.rdptr { bins rdptr_dist[] = {[0 : (1 << ADDR_WIDTH) - 1]}; }

    ptrs_cross: cross wrptr, rdptr;

  endgroup: ptrs_cg

  wr_port_cg wr_port_cg_i = new();
  rd_port_cg rd_port_cg_i = new();
  ptrs_cg ptrs_cg_i = new();

endmodule: cov_sfifo
