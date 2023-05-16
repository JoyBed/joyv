module rv32i_prototype5(
  clk,
  rst,
  read,
  write,
  data_bus_in,
  data_bus_out,
  addr_bus_out
);
  
  // Bitness of CPU
  parameter XLEN = 32; // RV32 -> 32, RV64 -> 64, RV128 -> 128
  
  // IO of the CPU
  input clk;
  input rst;
  output read;
  output write;
  input data_bus_in;
  output data_bus_out;
  output addr_bus_out;
  wire clk;
  wire rst;
  wire read;
  wire write;
  wire [XLEN-1:0] data_bus_in;
  wire [XLEN-1:0] data_bus_out;
  wire [XLEN-1:0] addr_bus_out;
  
  // Registers
  reg [XLEN-1:0] pc;
  reg [XLEN-1:0] next_pc;
  reg [XLEN-1:0] instr_reg;
  reg [XLEN-1:0] mem_data;
  reg [XLEN-1:0] mem_addr;
  reg [XLEN-1:0] register [0:31];
  reg [63:0] cycle_counter;
  reg [63:0] next_cycle_counter;
  reg [63:0] instruction_counter;
  reg [63:0] next_instruction_counter;
  reg [XLEN-1:0] data_bus_in_reg;
  reg [XLEN-1:0] data_bus_out_reg;
  reg [XLEN-1:0] addr_bus_out_reg;
  reg [6:0] opcode;
  reg [2:0] funct3;
  reg [6:0] funct7;
  reg [4:0] rs1_addr;
  reg [4:0] rs2_addr;
  reg [4:0] rd_addr;
  reg [4:0] shamt;
  reg [11:0] imm_i;
  reg [11:0] imm_s;
  reg [11:0] imm_sb;
  reg [19:0] imm_u;
  reg [19:0] imm_uj;
  reg [XLEN-1:0] target_addr;
  reg [XLEN-1:0] offset;
  reg branch_taken;
  reg instruction_taken;
  
  // Control signals
  reg bus_read;
  reg bus_write;

  // Internal variables
  integer i = 0;
  parameter SHAMT_MASK = 5'b00000_11111; // Mask for extracting the shamt field from bits 20-24 of the instruction

  // Extension modules -------------------------------------------------------------------------------------
  
  // RV32M - Multiply and division
  wire overflow;   // internal register for holding the overflow flag
  wire carry;      // internal register for holding the carry flag
  reg [31:0] ext_instr_reg;
  reg [31:0] operand1_reg;
  reg [31:0] operand2_reg;
  wire [31:0] result_wire;
  
  rv32m_extension rv32m_extension(
    .clk (clk), // clock
    .rst (rst), //reset 
    .instruction (ext_instr_reg), // instruction
    .operand1 (operand1_reg), // first operand
    .operand2 (operand2_reg), // second operand
    .result (result_wire), // result of the operation
    .overflow (overflow), // overflow flag for MULH and MULHSU
    .carry (carry) // carry flag for DIVU and REMU
   );
  
  // MMU
  /*wire mem_en;
  wire mmu_en;
  wire [31:0] addr_bus_out_wire;
  assign mmu_en = 1'b1;
  assign addr_bus_out = addr_bus_out_wire;
  
  rv32_mmu (
    .clk (clk),
    .rst (rst),
    .en (mmu_en),
    .addr_in (addr_bus_out_reg),
    .addr_out (addr_bus_out_wire),
    .mem_en (mem_en)
  );*/
  /*
  // Cache
  wire cache_hit;
  wire cache_miss;
  wire [31:0] cache_data;
  
  rv32_cache (
    .clk (clk),
    .rst (rst),
    .addr (addr_bus_out_wire),
    //.addr (addr_bus_out),
    .data_in (data_bus_in_reg),
    .we (bus_write),
    .data_out (cache_data),
    .hit (cache_hit),
    .miss (cache_miss)
  );*/

  
  // CPU Stages -----------------------------------------------------------------------------------------------
  
  // Fetch (clockless)
  always @(*) begin
    if (rst) begin
	  data_bus_in_reg <= 32'b0;
	  instr_reg <= 32'b0;
	  mem_data <= 32'b0;
	end else begin
      data_bus_in_reg = data_bus_in;
      instr_reg = data_bus_in_reg;
      mem_data = data_bus_in_reg;
      /*case ({cache_hit, cache_miss})
        2'b01: begin // cache miss, read from external memory
          instr_reg = data_bus_in_reg;
          mem_data = data_bus_in_reg;
        end
        2'b10: begin // cache hit, read from cache
          instr_reg = cache_data;
          mem_data = cache_data;
        end
        default: begin
          instr_reg = data_bus_in_reg;
          mem_data = data_bus_in_reg;
        end
      endcase*/
	end
  end
  
  // Decode (clockless)
  always @(*) begin
    if (rst) begin
	  opcode <= 32'b0;
      funct3 <= 32'b0;
      funct7 <= 32'b0;
      rd_addr <= 32'b0;
      rs1_addr <= 32'b0;
      rs2_addr <= 32'b0;
      shamt <= 32'b0;
      imm_i <= 32'b0;
      imm_s <= 32'b0;
      imm_sb <= 32'b0;
      imm_u <= 32'b0;
      imm_uj <= 32'b0;
	end else begin
      opcode <= instr_reg[6:0]; // Extract the opcode field from the instruction
      funct3 <= instr_reg[14:12]; // Extract the funct3 field from the instruction
      funct7 <= instr_reg[31:25]; // Extract the funct7 field from the instruction
      rd_addr <= instr_reg[11:7]; // Extract the rd address field from the instruction
      rs1_addr <= instr_reg[19:15]; // Extract the rs1 address field from the instruction
      rs2_addr <= instr_reg[24:20]; // Extract the rs2 address field from the instruction
      shamt <= instr_reg[24:20] & SHAMT_MASK; // Extract the shamt field from the instruction
      imm_i <= {{20{1'b0}}, instr_reg[31:20]}; //  Extract the immediate value for I-type instructions
      imm_s <= {instr_reg[31], instr_reg[11:7], instr_reg[30:25]}; // Extract the immediate value for S-type instructions
      imm_sb <= {instr_reg[31], instr_reg[7], instr_reg[30:25], instr_reg[11:8]}; // Extract the immediate value for SB-type instructions
      imm_u <= {instr_reg[31:12], 12'b0}; //  Extract the immediate value for U-type instructions
      imm_uj <= {instr_reg[31], instr_reg[19:12], instr_reg[20], instr_reg[30:21], instr_reg[10:1]}; // Extract the immediate value for UJ-type instructions
	end
  end

  // Execute
  always @(posedge clk) begin
    if (rst) begin
	  register[0] <= 32'b0;
      register[1] <= 32'b0;
      register[2] <= 32'b0;
      register[3] <= 32'b0;
      register[4] <= 32'b0;
      register[5] <= 32'b0;
      register[6] <= 32'b0;
      register[7] <= 32'b0;
      register[8] <= 32'b0;
      register[9] <= 32'b0;
      register[10] <= 32'b0;
      register[11] <= 32'b0;
      register[12] <= 32'b0;
      register[13] <= 32'b0;
      register[14] <= 32'b0;
      register[15] <= 32'b0;
      register[16] <= 32'b0;
      register[17] <= 32'b0;
      register[18] <= 32'b0;
      register[19] <= 32'b0;
      register[20] <= 32'b0;
      register[21] <= 32'b0;
      register[22] <= 32'b0;
      register[23] <= 32'b0;
      register[24] <= 32'b0;
      register[25] <= 32'b0;
      register[26] <= 32'b0;
      register[27] <= 32'b0;
      register[28] <= 32'b0;
      register[29] <= 32'b0;
      register[30] <= 32'b0;
      register[31] <= 32'b0;
	  pc <= 32'b0;
	  target_addr <= 32'b0;
	  instruction_taken <= 32'b0;
	  branch_taken <= 32'b0;
	  cycle_counter <= 32'b0;
	  next_cycle_counter <= 32'b0;
	  instruction_counter <= 32'b0;
	  next_instruction_counter <= 32'b0;
	  bus_write <= 32'b0;
	  bus_read <= 32'b0;
	  mem_addr <= 32'b0;
	  data_bus_out_reg <= 32'b0;
	  offset <= 32'b0;
	  ext_instr_reg <= 32'b0;
      operand1_reg <= 32'b0;
      operand2_reg <= 32'b0;
	end else begin
      next_cycle_counter = cycle_counter + 1; // Cycle counter
      cycle_counter = next_cycle_counter;
      case (opcode)
        7'b0110011: begin // R-type instructions part1
          case({funct7, funct3}) // ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND
            10'b0000000_000: begin // ADD
              register[rd_addr] <= register[rs1_addr] + register[rs2_addr];
              instruction_taken = 1;
            end
            10'b0100000_000: begin // SUB
              register[rd_addr] <= register[rs1_addr] - register[rs2_addr];
              instruction_taken = 1;
            end
            10'b0000000_001: begin // SLL
              register[rd_addr] <= register[rs1_addr] << (register[rs2_addr] & 32'h1F);
              instruction_taken = 1;
            end
            10'b0000000_010: begin // SLT
              register[rd_addr] <= (register[rs1_addr] < register[rs2_addr]) ? 1'b1 : 1'b0;
              instruction_taken = 1;
            end
            10'b0000000_011: begin // SLTU
              register[rd_addr] <= (register[rs1_addr] < register[rs2_addr]) ? 1'b1 : 1'b0;
              instruction_taken = 1;
            end
            10'b0000000_100: begin // XOR
              register[rd_addr] <= register[rs1_addr] ^ register[rs2_addr];
              instruction_taken = 1;
            end
            10'b0000000_101: begin // SRL
              register[rd_addr] <= register[rs1_addr] >> (register[rs2_addr] & 32'h1F);
              instruction_taken = 1;
            end
            10'b0100000_101: begin // SRA
              register[rd_addr] <= $signed(register[rs1_addr]) >>> (register[rs2_addr] & 32'h1F);
              instruction_taken = 1;
            end
            10'b0000000_110: begin // OR
              register[rd_addr] <= register[rs1_addr] | register[rs2_addr];
              instruction_taken = 1;
            end
            10'b0000000_111: begin // AND
              register[rd_addr] <= register[rs1_addr] & register[rs2_addr];
              instruction_taken = 1;
            end
            default: begin // pass to rv32m extension module
              ext_instr_reg <= instr_reg;
              operand1_reg <= register[rs1_addr];
              operand2_reg <= register[rs2_addr];
              register[rd_addr] <= result_wire;
              instruction_taken = 1;
            end
          endcase
        end
        7'b1100111: begin // I-type instructions part1
          case(funct3) // JALR
            3'b000: begin
              register[rd_addr] = pc + 4; // Set return address in rd
              pc = ((register[rs1_addr] + imm_i) >> 1) << 1; // Set new PC to (rs1 + imm) with lowest bit cleared
              instruction_taken = 1;
            end
            default: begin
              register[0] <= 32'b0;
            end
          endcase
        end
        7'b0000011: begin // I-type instructions part2
          case(funct3) // LB, LH, LW, LBU, LHU
            3'b000: begin // LB
              mem_addr = register[rs1_addr] + imm_i; // mem_addr = address from where to read
              bus_read = 1'b1; // Raise read signal
              register[rd_addr] = mem_data[7:0];
              instruction_taken = 1;
            end
            3'b001: begin // LH
              mem_addr = register[rs1_addr] + imm_i; // mem_addr = address from where to read
              bus_read = 1'b1; // Raise read signal
              register[rd_addr] = mem_data[15:0];
              instruction_taken = 1;
            end
            3'b010: begin // LW
              mem_addr = register[rs1_addr] + imm_i; // mem_addr = address from where to read
              bus_read = 1'b1; // Raise read signal
              register[rd_addr] = mem_data;
              instruction_taken = 1;
            end
            3'b100: begin // LBU
              mem_addr = register[rs1_addr] + imm_i; // mem_addr = address from where to read
              bus_read = 1'b1; // Raise read signal
              register[rd_addr] = {24'b0, mem_data[7:0]};
              instruction_taken = 1;
            end
            3'b101: begin // LHU
              mem_addr = register[rs1_addr] + imm_i; // mem_addr = address from where to read
              bus_read = 1'b1; // Raise read signal
              register[rd_addr] = {16'b0, mem_data[15:0]};
              instruction_taken = 1;
            end
            default: begin
              register[0] <= 32'b0;
            end
          endcase
        end
        7'b0010011: begin // Mix R and I - they have same opcode
          case(funct3) // ADDI, SLTI, SLTIU, XORI, ORI, ANDI
            3'b000: begin // ADDI I-type part2
              register[rd_addr] <= register[rs1_addr] + imm_i;
              instruction_taken = 1;
            end
            3'b001: begin // SLLI R-type part2
              register[rd_addr] <= register[rs1_addr] << shamt; // Left shift rs1 by shamt
              instruction_taken = 1; // Increase instruction counter after every executed instruction
            end
            3'b010: begin // SLTI I-type part2
              register[rd_addr] <= (register[rs1_addr] < imm_i) ? 1'b1 : 1'b0;
              instruction_taken = 1;
            end
            3'b011: begin // SLTIU I-type part2
              register[rd_addr] <= (register[rs1_addr] < imm_i) ? 1'b1 : 1'b0;
              instruction_taken = 1;
            end
            3'b100: begin // XORI I-type part2
              register[rd_addr] <= register[rs1_addr] ^ imm_i;
              instruction_taken = 1;
            end
            3'b101: begin
              case(funct7)
                7'b0000000: begin // SRLI R-type part2
                  register[rd_addr] <= register[rs1_addr] >> shamt; // Right shift rs1 by shamt
                  instruction_taken = 1;
                end
                7'b0100000: begin // SRAI R-type part2
                  register[rd_addr] <= $signed(register[rs1_addr]) >>> shamt; // Signed right shift rs1 by shamt
                  instruction_taken = 1;
                end
              endcase
            end
            3'b110: begin // ORI I-type part2
              register[rd_addr] <= register[rs1_addr] | imm_i;
              instruction_taken = 1;
            end
            3'b111: begin // ANDI I-type part2
              register[rd_addr] <= register[rs1_addr] & imm_i;
              instruction_taken = 1;
            end
            default: begin
              register[0] <= 32'b0;
            end
          endcase
        end
        7'b0100011: begin // S-type instructions
          case(funct3) // SB, SH, SW
            3'b000: begin // SB
              offset = {{20{instr_reg[31]}}, instr_reg[7], instr_reg[30:25], instr_reg[11:8], 2'b0};
              mem_addr = register[rs1_addr] + offset;
              data_bus_out_reg = {{19{register[rs2_addr][7]}}, register[rs2_addr][7:0]};
              bus_write = 1'b1; // Raise memory write signal
              instruction_taken = 1;
            end
            3'b001: begin // SH
              offset = {{20{instr_reg[31]}}, instr_reg[7], instr_reg[30:25], instr_reg[11:8], 2'b0};
              mem_addr = register[rs1_addr] + offset;
              data_bus_out_reg = {{16{register[rs2_addr][7]}}, register[rs2_addr][7:0]};
              bus_write = 1'b1; // Raise memory write signal
              instruction_taken = 1;
            end
            3'b010: begin // SW
              offset = {{20{instr_reg[31]}}, instr_reg[7], instr_reg[30:25], instr_reg[11:8], 2'b0};
              mem_addr = register[rs1_addr] + offset;
              data_bus_out_reg = {{19{register[rs2_addr][7]}}, register[rs2_addr][7:0], register[rs2_addr][31:8]};
              bus_write = 1'b1; // Raise memory write signal
              instruction_taken = 1;
            end
            default: begin
              register[0] <= 32'b0;
            end
          endcase
        end
        7'b1100011: begin // SB-type instructions
          case(funct3) // BEQ, BNE, BLT, BGE, BLTU, BGEU
            3'b000: begin // BEQ
              target_addr = pc + imm_sb;
              if (register[rs1_addr] == register[rs2_addr]) begin
                branch_taken = 1;
              end
              instruction_taken = 1;
            end
            3'b001: begin // BNE
              target_addr = pc + imm_sb;
              if (register[rs1_addr] != register[rs2_addr]) begin
                branch_taken = 1;
              end
              instruction_taken = 1;
            end
            3'b100: begin // BLT
              target_addr = pc + imm_sb;
              if ($signed(register[rs1_addr]) < $signed(register[rs2_addr])) begin
                branch_taken = 1;
              end
              instruction_taken = 1;
            end
            3'b101: begin // BGE
              target_addr = pc + imm_sb;
              if ($signed(register[rs1_addr]) >= $signed(register[rs2_addr])) begin
                branch_taken = 1;
              end
              instruction_taken = 1;
            end
            3'b110: begin // BLTU
              target_addr = pc + imm_sb;
              if (register[rs1_addr] < register[rs2_addr]) begin
                branch_taken = 1;
              end
              instruction_taken = 1;
            end
            3'b111: begin // BGEU
              target_addr = pc + imm_sb;
              if (register[rs1_addr] >= register[rs2_addr]) begin
                branch_taken = 1;
              end
              instruction_taken = 1;
            end
            default: begin
              register[0] <= 32'b0;
            end
          endcase
        end
        7'b0110111: begin // U-type instructions - LUI
          register[rd_addr] = {imm_u, 12'h0}; // Load imm into upper 20 bits of rd, and clear lower 12 bits
          instruction_taken = 1;
        end
        7'b0010111: begin // U-type instructions - AUIPC
          register[rd_addr] = pc + {imm_u, 12'h0}; // Add imm to PC and store the result in rd
          instruction_taken = 1;
        end
        7'b1101111: begin // UJ-type instructions - JAL
          register[rd_addr] = pc + 4; // Set return address in rd
          pc = ((pc + imm_uj) >> 1) << 1; // Calculate new PC
          instruction_taken = 1;
        end
        7'b1110011: begin // SCALL, SBREAK, RDCYCLE, RDCYCLEH, RDTIME, RDTIMEH, RDINSTRET, RDINSTRETH
          case (instr_reg[31:12])
            20'b000000000000_00000_000: begin // SCALL
              // TODO
              instruction_taken = 1;
            end
            20'b000000000001_00000_000: begin // SBREAK
              // TODO
              instruction_taken = 1;
            end
            20'b110000000000_00000_010: begin // RDCYCLE
              register[rd_addr] = cycle_counter[31:0];
              instruction_taken = 1;
            end
            20'b110010000000_00000_010: begin // RDCYCLEH
              register[rd_addr] = cycle_counter[63:32];
              instruction_taken = 1;
            end
            20'b110000000001_00000_010: begin // RDTIME
              // TODO
              instruction_taken = 1;
            end
            20'b110010000001_00000_010: begin // RDTIMEH
              // TODO
              instruction_taken = 1;
            end
            20'b110000000010_00000_010: begin // RDINSTRET
              register[rd_addr] = instruction_counter[31:0];
              instruction_taken = 1;
            end
            20'b110010000010_00000_010: begin // RDINSTRETH
              register[rd_addr] = instruction_counter[63:32];
              instruction_taken = 1;
            end
            default: begin
              register[0] <= 32'b0;
            end
          endcase
        end
        default: begin
          register[0] <= 32'b0;
        end
      endcase
      // Update instruction counter
      if (instruction_taken) begin
        next_instruction_counter = instruction_counter + 1;
        instruction_counter = next_instruction_counter;
        instruction_taken = 0;
      end
      // Update program counter
      pc = pc + 4;
	end
  end

  // Writeback (clockless)
  always @(*) begin
    if (rst) begin
      next_pc <= 32'b0;
	  addr_bus_out_reg <= 32'b0;
    end else begin
      if (bus_read | bus_write) begin
        addr_bus_out_reg = mem_addr;
      end else if (branch_taken) begin
        addr_bus_out_reg = target_addr;
      end else begin
        next_pc = pc / 4;
        addr_bus_out_reg = next_pc;
      end
	end
  end

// Signals for bus
//assign addr_bus_out = next_pc;
//assign addr_bus_out_wire = addr_bus_out_reg;
assign addr_bus_out = addr_bus_out_reg;
assign data_bus_out = data_bus_out_reg;
assign write = bus_write;
assign read = bus_read;

endmodule