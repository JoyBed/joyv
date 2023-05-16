module rv32m_extension (
  input         clk,           // clock input
  input         rst,           // reset input
  input  [31:0] instruction,   // instruction input
  input  [31:0] operand1,      // first operand
  input  [31:0] operand2,      // second operand
  output [31:0] result,        // result of the operation
  output        overflow,      // overflow flag for MULH and MULHSU
  output        carry          // carry flag for DIVU and REMU
);

  // This module implements the RV32M extension
  
  // Registers
  reg [63:0]   result_reg;     // internal register for holding the result
  reg          overflow_reg;   // internal register for holding the overflow flag
  reg          carry_reg;      // internal register for holding the carry flag
  reg [6:0]    opcode;         // Extract the opcode field from the instruction
  reg [2:0]    funct3;         // Extract the funct3 field from the instruction
  reg [6:0]    funct7;         // Extract the funct7 field from the instruction
  
// Fetch from CPU and decode 
  always @(*) begin
    if (rst) begin
      opcode <= 32'b0;
      funct3 <= 32'b0;
      funct7 <= 32'b0;
    end else begin
      opcode <= instruction[6:0];
      funct3 <= instruction[14:12];
      funct7 <= instruction[31:25];
    end
  end

// Execute and writeback  
always @(posedge clk) begin
  if (rst) begin
    result_reg <= 32'b0;
    overflow_reg <= 32'b0;
    carry_reg <= 32'b0;
  end else begin
    case({opcode, funct3, funct7})
      17'b0110011_000_0000001: begin // MUL
        result_reg = operand1 * operand2;
      end
      17'b0110011_001_0000001: begin // MULH
        result_reg = ($signed(operand1) * $signed(operand2)) >> 32;
        overflow_reg = ((($signed(operand1) * $signed(operand2)) >> 31) ^ (($signed(operand1) << 31) >> 31)) & 1'b1;
      end
      17'b0110011_010_0000001: begin // MULHSU
        result_reg = ($signed(operand1) * $unsigned(operand2)) >> 32;
        overflow_reg = ((($signed(operand1) * $unsigned(operand2)) >> 31) ^ (($signed(operand1) << 31) >> 31)) & 1'b1;
      end
      17'b0110011_011_0000001: begin // MULHU
        result_reg = ($unsigned(operand1) * $unsigned(operand2)) >> 32;
      end
      // DIV instruction
      17'b0110011_100_0000001: begin // DIV
        if (operand2 != 0) begin
          result_reg <= operand1 / operand2;
          carry_reg <= 0;
        end else begin
          result_reg <= {32{1'b1}};
          carry_reg <= 1;
        end
      end
      17'b0110011_101_0000001: begin // DIVU
        if (operand2 != 0) begin
          result_reg <= $unsigned(operand1) / $unsigned(operand2);
          carry_reg <= 0;
        end else begin
          result_reg <= {32{1'b1}};
          carry_reg <= 1;
        end
      end
      17'b0110011_110_0000001: begin 
        result_reg = operand1 % operand2; // REM
      end
      17'b0110011_111_0000001: begin
        result_reg = $unsigned(operand1 % operand2); // REMU
      end
    endcase
  end
end

assign result = result_reg[31:0]; // assign the result to the output port
assign overflow = overflow_reg; // assign overflow flag to the output port for MULH and MULHSU
assign carry = carry_reg; // assign carry flag to the output port for DIVU and REMU

endmodule
