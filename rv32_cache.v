module rv32_cache (
  input clk,
  input rst,
  input [31:0] addr,
  input [31:0] data_in,
  input we,
  output reg [31:0] data_out,
  output reg hit,
  output reg miss
);

// cache parameters
parameter ASSOC = 4; // set-associativity
parameter CACHE_SIZE = 8192; // total cache size
parameter LINE_SIZE = 32; // 32-byte cache lines
parameter CACHE_LINES = CACHE_SIZE / LINE_SIZE; // number of lines
parameter INDEX_WIDTH = $clog2(CACHE_LINES / ASSOC); // number of bits for index
parameter TAG_WIDTH = 32 - INDEX_WIDTH - $clog2(LINE_SIZE); // number of bits for tag
parameter OFFSET_WIDTH = $clog2(LINE_SIZE); // number of bits for offset
parameter OFFSET_MASK = (1 << OFFSET_WIDTH) - 1; // mask for offset bits

// cache memory with valid bits
reg [LINE_SIZE-1:0] cache_mem [0:CACHE_LINES/ASSOC-1][0:ASSOC-1];
reg [TAG_WIDTH-1:0] tag_mem [0:CACHE_LINES/ASSOC-1][0:ASSOC-1];
reg [0:ASSOC-1] valid_mem [0:CACHE_LINES/ASSOC-1];

// cache control signals
wire [TAG_WIDTH-1:0] tag = addr[31:INDEX_WIDTH+OFFSET_WIDTH];
wire [INDEX_WIDTH-1:0] index = addr[INDEX_WIDTH+OFFSET_WIDTH-1:OFFSET_WIDTH]; // number of bits for index
wire [OFFSET_WIDTH-1:0] offset = addr[OFFSET_WIDTH-1:0]; // apply offset mask

// LRU variables and signals
parameter ASSOC_LOG = $clog2(ASSOC);
parameter INDEX_SIZE = CACHE_LINES / ASSOC; // number of indices
reg [ASSOC_LOG-1:0] lru_count [0:INDEX_SIZE-1]; // Declare LRU counter array
integer lru = -1;
integer i = 0;
integer j = 0;
reg hit_found;

// cache output
always @ (posedge clk) begin
  data_out <= cache_mem[index][offset];
end

// cache write
always @ (posedge clk) begin
  if (rst) begin
    // Reset LRU counters on reset
    for (i = 0; i < INDEX_SIZE; i = i + 1) begin
      for (j = 0; j < ASSOC; j = j + 1) begin
        lru_count[i][j] <= 0;
        cache_mem[i][j] <= 0;
        tag_mem[i][j] <= 0;
        valid_mem[i][j] <= 0;
      end
    end
  end else if (we) begin
    // Find an empty or least recently used (LRU) cache line
    lru = -1;
    hit_found = 0;
    for (i = 0; i < ASSOC; i = i + 1) begin
      if (tag_mem[index][i] == tag && valid_mem[index][i] == 1) begin
        // Cache hit - update LRU counter and cache line
        lru_count[index][i] <= 0;
        hit <= 1;
        miss <= 0;
        hit_found = 1;
        for (j = 0; j < LINE_SIZE; j = j + 8) begin
          cache_mem[index][i][j +: 8] <= data_in[j +: 8];
        end
      end else begin
        // Cache miss or empty cache line - check LRU counter
        if (lru == -1 || lru_count[index][i] > lru_count[index][lru]) begin
          lru = i;
        end
      end
      // Increment LRU counter for each cache line in the set
      lru_count[index][i] <= lru_count[index][i] + 1;
    end
    if (!hit_found) begin
      // Cache miss - evict LRU cache line and update cache line and LRU counter
      for (j = 0; j < LINE_SIZE; j = j + 8) begin
        cache_mem[index][lru][j +: 8] <= data_in[j +: 8];
      end
      tag_mem[index][lru] <= tag;
      valid_mem[index][lru] <= 1;
      lru_count[index][lru] <= 0;
      hit <= 0;
      miss <= 1;
    end
  end
end

// Cache hit and miss detection
always @(*) begin
  hit = 0;
  miss = 1;
  for (i = 0; i < ASSOC && !hit; i = i + 1) begin
    if (tag_mem[index][i] == tag && valid_mem[index][i] == 1) begin
      hit = 1;
      miss = 0;
    end
  end
end

endmodule