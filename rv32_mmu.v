module rv32_mmu (
  input              clk,
  input              rst,
  input              en,
  input      [31:0]  addr_in,
  output reg [31:0]  addr_out,
  output reg         mem_en
);

  // Define the page size and number of pages
  parameter PAGE_SIZE   = 4096;
  parameter NUM_PAGES   = 16;
  
  integer i = 0;
  integer j = 0;
  integer rst_i = 0;
  reg hit;
  
  // Define the page table, TLB and initialize to all zeros
  parameter NUM_TLB_ENTRIES = 8;
  reg [19:0] tlb_tags [0:NUM_TLB_ENTRIES-1];
  reg [31:0] tlb_ppns [0:NUM_TLB_ENTRIES-1];
  reg [31:0] page_table [0:NUM_PAGES-1];
  
  // Define the page offset and page index
  reg [11:0] page_offset;
  reg [3:0] page_index;
  
  wire [31:0] rand_num;
  rng rng (
    .clk (clk),
    .rst (rst),
    .rand_num (rand_num)
  );
  
  // Output the virtual address if address translation is disabled
  always @(posedge clk) begin
    if (rst) begin
      addr_out <= 32'h0;
      mem_en   <= 1'b0;
    end else if (!en) begin
      addr_out <= addr_in;
      mem_en   <= 1'b1;
    end
  end
  
  // Translate the virtual address using the TLB if address translation is enabled
  always @(posedge clk) begin
    if (rst) begin
      for (rst_i = 0; rst_i < NUM_PAGES; rst_i = rst_i + 1) begin
        page_table[rst_i] = 32'h0;
        tlb_tags[rst_i] <= 32'h0;
        tlb_ppns[rst_i] <= 32'h0;
      end
      rst_i = 0; // Reset the index variable
      i = 0;
      j = 0;
      hit = 0;
    end else if (en) begin
      page_offset = addr_in[11:0];
      page_index = addr_in[15:12];
      // Check the TLB for a hit
      hit = 0;
      i = 0; // Reset the index variable
      while (i < NUM_TLB_ENTRIES && !hit) begin
        if (tlb_tags[i] == addr_in[31:12]) begin
          addr_out <= {tlb_ppns[i], page_offset};
          mem_en   <= 1'b1;
          hit      <= 1;
        end
        i = i + 1;
      end
      i = 0;
      // If the TLB lookup failed, perform a page table walk and update the TLB
      if (!hit) begin
        // Look up the physical page number in the page table
        addr_out <= {(page_table[page_index] << 12) + page_offset};
        mem_en   <= 1'b1;
        // If the page is not present, allocate a new page
        if (page_table[page_index] == 32'h0) begin
          page_table[page_index] = rand_num; // For simplicity, we use a random value here
        end
        // Update the TLB with the new entry
        tlb_tags[0] <= addr_in[31:12];
        tlb_ppns[0] <= page_table[page_index];
        // Shift the entries in the TLB
        for (j = NUM_TLB_ENTRIES-1; j > 0; j = j - 1) begin
          tlb_tags[j] <= tlb_tags[j-1];
          tlb_ppns[j] <= tlb_ppns[j-1];
        end
        j = 0;
      end
    end
  end
  
endmodule

//random number generator
module rng (
  input clk,
  input rst,
  output reg [31:0] rand_num
);

  reg [31:0] seed = 1;

  always @(posedge clk) begin
    if (rst) begin
      seed <= 1;
      rand_num <= 0;
    end else begin
      seed <= {seed[30:0], seed[0] ^ seed[1] ^ seed[3] ^ seed[4]};
      rand_num <= seed;
    end
  end

endmodule