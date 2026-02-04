module cov_mem_sys (
  input logic clk,
  input logic arst_n,

  // Main memory signals
  // Reading port //
  input logic main_mem_rden,
  input logic [MAIN_MEM_ADDR_WIDTH - 1 : 0] main_mem_rd_addr,
  input logic [MAIN_MEM_DATA_WIDTH - 1 : 0] main_mem_rd_data,
  input logic main_mem_rd_data_valid,
  
  // Writing port //
  input logic main_mem_wren,
  input logic [MAIN_MEM_ADDR_WIDTH - 1 : 0] main_mem_wr_addr,
  input logic [MAIN_MEM_DATA_WIDTH - 1 : 0] main_mem_wr_data,
  input logic main_mem_wr_data_ack,

  // accumulation raw dependencies
  input logic rpg_pre_stall [NUM_READ_BUFFERS],
  input logic rpg_stall [NUM_READ_BUFFERS],

  // write pattern generator signals
  input logic [MAIN_MEM_ADDR_WIDTH - 1 : 0] wpg_st_addr [NUM_WRITE_BUFFERS],
  input logic [MAIN_MEM_ADDR_WIDTH - 1 : 0] wpg_burst_length [NUM_WRITE_BUFFERS],
  input logic wpg_busy [NUM_WRITE_BUFFERS],
  input logic wpg_ack [NUM_WRITE_BUFFERS],

  // read pattern generator signals
  input logic [MAIN_MEM_ADDR_WIDTH - 1 : 0] rpg_st_addr [NUM_READ_BUFFERS],
  input logic [MAIN_MEM_ADDR_WIDTH - 1 : 0] rpg_burst_length [NUM_READ_BUFFERS],
  input logic rpg_busy [NUM_READ_BUFFERS],
  input logic rpg_ack [NUM_READ_BUFFERS],

  // Writing port for writing buffers //
  input logic wr_buff_wren [NUM_WRITE_BUFFERS],
  input logic [MAIN_MEM_DATA_WIDTH - 1 : 0] wr_buff_wdata [NUM_WRITE_BUFFERS],
  input logic wr_buff_pre_full [NUM_WRITE_BUFFERS],
  input logic wr_buff_full [NUM_WRITE_BUFFERS],
  input logic wr_buff_rden [NUM_WRITE_BUFFERS], // TODO: this is not necessary to be an output, but I will put it as an output for verification purposes
  input logic [MAIN_MEM_DATA_WIDTH - 1 : 0] wr_buff_rdata [NUM_WRITE_BUFFERS], // TODO: this is not necessary to be an output, but I will put it as an output for verification purposes
  input logic wr_buff_pre_empty [NUM_WRITE_BUFFERS], // TODO: this is not necessary to be an output, but I will put it as an output for verification purposes
  input logic wr_buff_empty [NUM_WRITE_BUFFERS], // TODO: this is not necessary to be an output, but I will put it as an output for verification purposes

  // Reading port for reading buffers //
  input logic rd_buff_rden [NUM_READ_BUFFERS],
  input logic [MAIN_MEM_DATA_WIDTH - 1 : 0] rd_buff_rdata [NUM_READ_BUFFERS],
  input logic rd_buff_pre_empty [NUM_READ_BUFFERS],
  input logic rd_buff_empty [NUM_READ_BUFFERS],
  input logic rd_buff_wren [NUM_READ_BUFFERS], // TODO: this is not necessary to be an output, but I will put it as an output for verification purposes
  input logic [MAIN_MEM_DATA_WIDTH - 1 : 0] rd_buff_wdata [NUM_READ_BUFFERS], // TODO: this is not necessary to be an output, but I will put it as an output for verification purposes
  input logic rd_buff_pre_full [NUM_READ_BUFFERS], // TODO: this is not necessary to be an output, but I will put it as an output for verification purposes
  input logic rd_buff_full [NUM_READ_BUFFERS], // TODO: this is not necessary to be an output, but I will put it as an output for verification purposes

  // Window operation ports //
  input logic [$clog2(MAX_WR_QUANTUM)-1:0] wr_buff_writing_window [NUM_WRITE_BUFFERS],
  input logic [$clog2(MAX_RD_QUANTUM)-1:0] rd_buff_reading_window [NUM_READ_BUFFERS]
);

  `define BD_PATH buffers_discharger_i
  `define BF_PATH buffers_filler_i
  `define MEM_PATH main_memory_model_i
  `define BUFFERS_PATH mem_sys_i.buffers_i  
  `define READ_BUF_PATH mem_sys_i.buffers_i.READ_BUFFER
  `define WRITE_BUF_PATH mem_sys_i.buffers_i.WRITE_BUFFER

  localparam NUM_BINS_ADDRS = 16;
  localparam NUM_BINS_BURST_LENGTH = 8;


  // MEM_SYS coverage groups

  covergroup main_mem_read_cg; // This group samples the main memory read port signals
    option.per_instance = 1;
    main_mem_rden_change_state: coverpoint main_mem_rden {
    bins rise = (0 => 1);
    bins fall = (1 => 0);
    }

    main_mem_rden_value: coverpoint main_mem_rden {
      bins enabled = {1};
      bins disabled = {0};
    }

    coverpoint main_mem_rd_addr {
      bins each_addr[] = {[0 : (1 << MAIN_MEM_ADDR_WIDTH)-1]};
    }

    coverpoint main_mem_rd_data {
      bins low  = {[0 : (1 << (MAIN_MEM_DATA_WIDTH-2)) - 1]};
      bins mid  = {[(1 << (MAIN_MEM_DATA_WIDTH-2)) : (1 << (MAIN_MEM_DATA_WIDTH-1)) - 1]};
      bins high = {[(1 << (MAIN_MEM_DATA_WIDTH-1)) : (1 << MAIN_MEM_DATA_WIDTH) - 1]};
    }

    main_mem_rd_data_valid_change_state: coverpoint main_mem_rd_data_valid {
    bins valid_rose = (0 => 1);
    bins valid_fell = (1 => 0);
    }

    main_mem_rd_data_valid_value: coverpoint main_mem_rd_data_valid {
      bins valid = {1};
      bins invalid = {0};
    }

    ack_to_rden_cross: cross main_mem_rden_value, main_mem_rd_data_valid_value;

  endgroup: main_mem_read_cg


  covergroup main_mem_write_cg; // This group samples the main memory write port signals
    option.per_instance = 1;
    main_mem_wren_change_state: coverpoint main_mem_wren {
    bins rise = (0 => 1);
    bins fall = (1 => 0);
    }

    main_mem_wren_value: coverpoint main_mem_wren {
      bins enabled = {1};
      bins disabled = {0};
    }

    coverpoint main_mem_wr_addr {
      bins each_addr[] = {[0 : (1 << MAIN_MEM_ADDR_WIDTH)-1]};
    }

    coverpoint main_mem_wr_data {
      bins low_value  = {[0 : (1 << (MAIN_MEM_DATA_WIDTH-2)) - 1]};
      bins mid_value  = {[(1 << (MAIN_MEM_DATA_WIDTH-2)) : (1 << (MAIN_MEM_DATA_WIDTH-1)) - 1]};
      bins high_value = {[(1 << (MAIN_MEM_DATA_WIDTH-1)) : (1 << MAIN_MEM_DATA_WIDTH) - 1]};
    }

    main_mem_wr_data_ack_change_state: coverpoint main_mem_wr_data_ack {
    bins rise = (0 => 1);
    bins fall = (1 => 0);
    }

    main_mem_wr_data_ack_value: coverpoint main_mem_wr_data_ack {
      bins acked = {1};
      bins not_acked = {0};
    }

    ack_to_wren_cross: cross main_mem_wren_value, main_mem_wr_data_ack_value;
  endgroup: main_mem_write_cg


  covergroup stall_idx_cg (int idx); // This group samples the stall inputs for each index
    option.per_instance = 1;
    cp_pre_stall: coverpoint rpg_pre_stall[idx] {
      bins stall_rise = (0 => 1);
      bins stall_fall = (1 => 0);
    }
    cp_stall:     coverpoint rpg_stall[idx] {
      bins stall_rise = (0 => 1);
      bins stall_fall = (1 => 0);
    }
  endgroup: stall_idx_cg


  covergroup wpg_buff_dchrgr_port_cg (int idx) @(posedge clk); // This group samples the write pattern generator signals for each writing buffer
    option.per_instance = 1;

    busy_value: coverpoint wpg_busy[idx] {
      bins busy = {1};
      bins not_busy = {0};
    }

    busy_change: coverpoint wpg_busy[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }


    ack_value: coverpoint wpg_ack[idx] {
      bins acked = {1};
      bins not_acked = {0};
    }

    ack_change: coverpoint wpg_ack[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }

    starting_address: coverpoint wpg_st_addr[idx] {
      bins addr_16ths[NUM_BINS_ADDRS] = {[0 : ((1 << MAIN_MEM_ADDR_WIDTH))-1]};
    }

    initial_burst_length: coverpoint wpg_burst_length[idx] {
      bins len_8ths[NUM_BINS_BURST_LENGTH] = {[0 : ((1 << MAIN_MEM_ADDR_WIDTH))-1]};
    }
    
    ack_response_to_busy: cross busy_value, ack_value {
      ignore_bins idle_acked = binsof(busy_value.not_busy) && binsof(ack_value.acked); // Cannot ack when not busy
    }

    starting_address_to_burst_length: cross starting_address, initial_burst_length;

  endgroup: wpg_buff_dchrgr_port_cg


  covergroup rpg_buff_fllr_port_cg (int idx) @(posedge clk); // This group samples the read pattern generator signals for each reading buffer
    option.per_instance = 1;

    busy_value: coverpoint rpg_busy[idx] {
      bins busy = {1};
      bins not_busy = {0};
    }
    
    busy_change: coverpoint rpg_busy[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }

    ack_value: coverpoint rpg_ack[idx] {
      bins acked = {1};
      bins not_acked = {0};
    }
    
    ack_change: coverpoint rpg_ack[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }

    starting_address: coverpoint rpg_st_addr[idx] {
      bins addr_16ths[NUM_BINS_ADDRS] = {[0 : ((1 << MAIN_MEM_ADDR_WIDTH))-1]};
    }

    initial_burst_length: coverpoint rpg_burst_length[idx] {
      bins len_8ths[NUM_BINS_BURST_LENGTH] = {[0 : ((1 << MAIN_MEM_ADDR_WIDTH))-1]};
    }

    ack_response_to_busy: cross busy_value, ack_value {
      ignore_bins idle_acked = binsof(busy_value.not_busy) && binsof(ack_value.acked); // Cannot ack when not busy
    }

    starting_address_to_burst_length: cross starting_address, initial_burst_length;

  endgroup: rpg_buff_fllr_port_cg


  covergroup wr_buff_ports_cg (int idx);
    option.per_instance = 1;

    wren_value: coverpoint wr_buff_wren[idx] {
      bins enabled = {1};
      bins disabled = {0};
    }
    wren_change_state : coverpoint wr_buff_wren[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }

    pre_full_value: coverpoint wr_buff_pre_full[idx] {
      bins pre_full = {1};
      bins not_pre_full = {0};
    }
    pre_full_change_state : coverpoint wr_buff_pre_full[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }
    
    full_value: coverpoint wr_buff_full[idx] {
      bins full = {1};
      bins not_full = {0};
    }
    full_change_state : coverpoint wr_buff_full[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }

    cross pre_full_value, full_value { // Ignore case where both are full
      ignore_bins both_full = binsof(pre_full_value.pre_full) && binsof(full_value.full);
    }

    rden_value: coverpoint wr_buff_rden[idx] {
      bins enabled = {1};
      bins disabled = {0};
    }
    rden_change_state : coverpoint wr_buff_rden[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }

    pre_empty_value: coverpoint wr_buff_pre_empty[idx] {
      bins pre_empty = {1};
      bins not_pre_empty = {0};
    }
    pre_empty_change_state : coverpoint wr_buff_pre_empty[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }
    empty_value: coverpoint wr_buff_empty[idx] {
      bins empty = {1};
      bins not_empty = {0};
    }
    empty_change_state : coverpoint wr_buff_empty[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }

    cross pre_empty_value, empty_value { // Ignore case where both are empty
      ignore_bins both_empty = binsof(pre_empty_value.pre_empty) && binsof(empty_value.empty);
    }

  endgroup: wr_buff_ports_cg


  covergroup rd_buff_ports_cg (int idx) @(posedge clk);
    option.per_instance = 1;

    rden_value: coverpoint rd_buff_rden[idx] {
      bins enabled = {1};
      bins disabled = {0};
    }
    rden_change_state : coverpoint rd_buff_rden[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }

    pre_empty_value: coverpoint rd_buff_pre_empty[idx] {
      bins pre_empty = {1};
      bins not_pre_empty = {0};
    }
    pre_empty_change_state : coverpoint rd_buff_pre_empty[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }

    empty_value: coverpoint rd_buff_empty[idx] {
      bins empty = {1};
      bins not_empty = {0};
    }
    empty_change_state : coverpoint rd_buff_empty[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }

    cross pre_empty_value, empty_value { // Ignore case where both are empty
      ignore_bins both_empty = binsof(pre_empty_value.pre_empty) && binsof(empty_value.empty);
    }
    
    wren_value: coverpoint rd_buff_wren[idx] {
      bins enabled = {1};
      bins disabled = {0};
    }
    wren_change_state : coverpoint rd_buff_wren[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }
    
    pre_full_value: coverpoint rd_buff_pre_full[idx] {
      bins pre_full = {1};
      bins not_pre_full = {0};
    }
    pre_full_change_state : coverpoint rd_buff_pre_full[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }
    full_value: coverpoint rd_buff_full[idx] {
      bins full = {1};
      bins not_full = {0};
    }
    full_change_state : coverpoint rd_buff_full[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }
    
    cross pre_full_value, full_value { // Ignore case where both are full
      ignore_bins both_full = binsof(pre_full_value.pre_full) && binsof(full_value.full);
    }

  endgroup: rd_buff_ports_cg


  // BUFFERS_DISCHARGER coverage groups

  covergroup buffers_discharger_in_signals_cg (int idx) @(posedge clk);
    option.per_instance = 1;

    wpg_burst_ongoing_value: coverpoint `BD_PATH.wpg_burst_ongoing[idx] {
      bins ongoing = {1};
      bins not_ongoing = {0};
    }
    wpg_burst_ongoing_change: coverpoint `BD_PATH.wpg_burst_ongoing[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }

    wpg_burst_start_value: coverpoint `BD_PATH.wpg_burst_start[idx] {
      bins started = {1};
      bins not_started = {0};
    }
    wpg_burst_start_change: coverpoint `BD_PATH.wpg_burst_start[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }
    
    wpg_burst_done_value: coverpoint `BD_PATH.wpg_burst_done[idx] {
      bins done = {1};
      bins not_done = {0};
    }
    wpg_burst_done_change: coverpoint `BD_PATH.wpg_burst_done[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }

    written_addresses: coverpoint `BD_PATH.wpg_st_addr_r[idx] {
      bins each_addr[] = {[0 : (1 << MAIN_MEM_ADDR_WIDTH)-1]};
    }

    burst_lengths: coverpoint `BD_PATH.wpg_burst_length_r[idx] {
      bins each_len[] = {[0 : (1 << MAIN_MEM_ADDR_WIDTH)-1]};
    }

    //cp_state: coverpoint state;
  endgroup: buffers_discharger_in_signals_cg

  covergroup buffer_discharger_buffer_sel_cg @(posedge clk);
    option.per_instance = 1;
    selected_buffer: coverpoint `BD_PATH.wr_buff_sel {
      bins sel[] = {[0 : NUM_WRITE_BUFFERS-1]};
    }
  endgroup: buffer_discharger_buffer_sel_cg

  // BUFFERS_FILLER coverage groups

  covergroup buffers_filler_in_signals_cg (int idx) @(posedge clk);
    option.per_instance = 1;

    rpg_burst_ongoing_value: coverpoint `BF_PATH.rpg_burst_ongoing[idx] {
      bins ongoing = {1};
      bins not_ongoing = {0};
    }
    rpg_burst_ongoing_change: coverpoint `BF_PATH.rpg_burst_ongoing[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }

    rpg_burst_start_value: coverpoint `BF_PATH.rpg_burst_start[idx] {
      bins started = {1};
      bins not_started = {0};
    }
    rpg_burst_start_change: coverpoint `BF_PATH.rpg_burst_start[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }

    rpg_burst_done_value: coverpoint `BF_PATH.rpg_burst_done[idx] {
      bins done = {1};
      bins not_done = {0};
    }
    rpg_burst_done_change: coverpoint `BF_PATH.rpg_burst_done[idx] {
      bins rise = (0 => 1);
      bins fall = (1 => 0);
    }


    rpg_pre_stall_value: coverpoint `BF_PATH.rpg_pre_stall[idx] {
      bins pre_stall = {1};
      bins not_pre_stall = {0};
    }
    rpg_pre_stall_change: coverpoint `BF_PATH.rpg_pre_stall[idx] {
      bins stall_rise = (0 => 1);
      bins stall_fall = (1 => 0);
    }


    rpg_stall_value: coverpoint `BF_PATH.rpg_stall[idx] {
      bins stall = {1};
      bins not_stall = {0};
    }
    rpg_stall_change: coverpoint `BF_PATH.rpg_stall[idx] {
      bins stall_rise = (0 => 1);
      bins stall_fall = (1 => 0);
    }

    read_addresses: coverpoint `BF_PATH.rpg_st_addr_r[idx] {
      bins addr[] = {[0 : (1 << MAIN_MEM_ADDR_WIDTH)-1]};
    }

    burst_lengths: coverpoint `BF_PATH.rpg_burst_length_r[idx] {
      bins len[] = {[0 : (1 << MAIN_MEM_ADDR_WIDTH)-1]};
    }

    //cp_state: coverpoint state;
  endgroup: buffers_filler_in_signals_cg

  covergroup buffer_filler_buffer_sel_cg @(posedge clk);
    option.per_instance = 1;
    selected_buffer: coverpoint `BF_PATH.rd_buff_sel {
      bins sel[] = {[0 : NUM_READ_BUFFERS-1]};
    }
  endgroup: buffer_filler_buffer_sel_cg


  // Individual Sfifo coverage groups
  genvar i;
  generate
    for (i = 0; i < NUM_READ_BUFFERS; i++) begin : gen_read_cov

      covergroup rd_buff_ptrs_cg @(posedge clk);
      option.per_instance = 1;
        wr_ptr: coverpoint `READ_BUF_PATH[i].rd_buffer.wrptr;
        rd_ptr: coverpoint `READ_BUF_PATH[i].rd_buffer.rdptr;
        pntrs_cross: cross wr_ptr,rd_ptr;
      endgroup: rd_buff_ptrs_cg

      rd_buff_ptrs_cg read_buffers_ptrs_cg = new();

      always @(posedge clk) begin
        if (rpg_busy[i])
      read_buffers_ptrs_cg.sample();
      end
    end
  endgenerate
  generate
    for (i = 0; i < NUM_WRITE_BUFFERS; i++) begin : gen_write_cov
      covergroup wr_buff_ptrs_cg @(posedge clk);
      option.per_instance = 1;
        wr_ptr: coverpoint `WRITE_BUF_PATH[i].wr_buffer.wrptr;
        rd_ptr: coverpoint `WRITE_BUF_PATH[i].wr_buffer.rdptr;
        pntrs_cross: cross wr_ptr,rd_ptr;
      endgroup: wr_buff_ptrs_cg

      wr_buff_ptrs_cg write_buffers_ptrs_cg = new();

      always @(posedge clk) begin
        if (wpg_busy[i])
      write_buffers_ptrs_cg.sample();
      end
    end
  endgenerate


  // ====== Instantiate coverage groups ======
    // MEM_SYS coverage group handles
  main_mem_read_cg main_mem_read_port;
  main_mem_write_cg main_mem_write_port;
  
  stall_idx_cg stall_input_cgs [NUM_READ_BUFFERS];
  wpg_buff_dchrgr_port_cg wpg_buff_dchrgr_port_cgs [NUM_WRITE_BUFFERS];
  rpg_buff_fllr_port_cg rpg_buff_fllr_port_cgs [NUM_READ_BUFFERS];

  wr_buff_ports_cg wr_buff_ports_cgs [NUM_WRITE_BUFFERS];
  rd_buff_ports_cg rd_buff_ports_cgs [NUM_READ_BUFFERS];
    // BUFFERS_DISCHARGER coverage group handles
  buffers_discharger_in_signals_cg bd_cgs [NUM_WRITE_BUFFERS];
  buffer_discharger_buffer_sel_cg bd_buffer_sel_cg_inst;
    // BUFFERS_FILLER coverage group handles
  buffers_filler_in_signals_cg bf_cgs [NUM_READ_BUFFERS];
  buffer_filler_buffer_sel_cg bf_buffer_sel_cg_inst;


  // Instantiate coverage groups
  initial begin
    // MEM_SYS coverage instances
    main_mem_read_port = new();
    main_mem_write_port = new();
    // BUFFERS_DISCHARGER coverage group instances
    bd_buffer_sel_cg_inst = new();
    // BUFFERS_FILLER coverage group instances
    bf_buffer_sel_cg_inst = new();

    for(int i = 0; i < NUM_READ_BUFFERS; i++) begin
      stall_input_cgs[i] = new(i);
      rpg_buff_fllr_port_cgs[i] = new(i);
      rd_buff_ports_cgs[i] = new(i);
      bf_cgs[i] = new(i);
    end
    for(int j = 0; j < NUM_WRITE_BUFFERS; j++) begin
      wpg_buff_dchrgr_port_cgs[j] = new(j);
      wr_buff_ports_cgs[j] = new(j);
      bd_cgs[j] = new(j);
    end

  end  


  logic wpg_any_busy;
  logic rpg_any_busy;

  always_comb begin
    wpg_any_busy = 1'b0;
    for (int i = 0; i < NUM_WRITE_BUFFERS; i++)
      wpg_any_busy |= wpg_busy[i];

    rpg_any_busy = 1'b0;
    for (int i = 0; i < NUM_READ_BUFFERS; i++)
      rpg_any_busy |= rpg_busy[i];
  end

  initial begin // MEM_SYS coverage group sampling
    forever begin
      @(posedge clk);
      if (wpg_any_busy) begin
        main_mem_read_port.sample();
      end
      if (rpg_any_busy) begin
        main_mem_write_port.sample();
      end
      for(int i = 0; i < NUM_READ_BUFFERS; i++) begin
        if (rpg_busy[i])
          stall_input_cgs[i].sample();
      end  
    end
  end 

  initial begin // WPG buffer discharger coverage group sampling
    forever begin
      @(posedge clk);
      if (wpg_any_busy) begin
        bd_buffer_sel_cg_inst.sample();
      end  
      for (int i = 0; i < NUM_WRITE_BUFFERS; i++) begin
        if (wpg_busy[i]) begin
          wpg_buff_dchrgr_port_cgs[i].sample();
          bd_cgs[i].sample();
        end
      end
    end
  end

  initial begin // RPG buffer filler coverage group sampling
    forever begin
      @(posedge clk);
      if (rpg_any_busy) begin
        bf_buffer_sel_cg_inst.sample();
      end
      for (int i = 0; i < NUM_READ_BUFFERS; i++) begin
        rpg_buff_fllr_port_cgs[i].sample();
        bf_cgs[i].sample();
      end
    end
  end

  initial begin // Individual Sfifo coverage group sampling
      forever begin
        @(posedge clk);
        for(int i = 0; i < NUM_WRITE_BUFFERS; i++) begin
          if (wpg_busy[i]) begin
            wr_buff_ports_cgs[i].sample();
          end
        end
        for(int i = 0; i < NUM_READ_BUFFERS; i++) begin
          if (rpg_busy[i]) begin
            rd_buff_ports_cgs[i].sample();
          end
        end
      end
  end


endmodule: cov_mem_sys
