//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: test_data.sv
// Module: test_data
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Shared test vectors and stimulus data for unit and integration testbenches.
//   Includes ALU, register file, and memory test vectors. Extend as needed.
//=============================================================================

package test_data;
    //===========================================================================
    // ALU Test Vectors
    //===========================================================================
    typedef struct packed {
        logic [31:0] a;
        logic [31:0] b;
        logic [3:0] op;
        logic [31:0] expected;
        logic expected_zero;
        logic expected_overflow;
    } alu_vec_t;

    // Example ALU test vectors (add, sub, and, or, xor, shifts, slt, sltu)
    const alu_vec_t alu_vectors[] = '{
        '{32'h0000_0001, 32'h0000_0002, 4'd0, 32'h0000_0003, 1'b0, 1'b0}, // ADD
        '{32'h0000_0005, 32'h0000_0002, 4'd1, 32'h0000_0003, 1'b0, 1'b0}, // SUB
        '{32'hFFFF_FFFF, 32'h0000_FFFF, 4'd2, 32'h0000_FFFF, 1'b0, 1'b0}, // AND
        '{32'h0000_FFFF, 32'hFFFF_0000, 4'd3, 32'hFFFF_FFFF, 1'b0, 1'b0}, // OR
        '{32'hFFFF_FFFF, 32'hFFFF_FFFF, 4'd4, 32'h0000_0000, 1'b1, 1'b0}, // XOR
        '{32'h0000_0001, 32'h0000_0004, 4'd5, 32'h0000_0010, 1'b0, 1'b0}, // SLL
        '{32'h0000_0010, 32'h0000_0002, 4'd6, 32'h0000_0004, 1'b0, 1'b0}, // SRL
        '{32'hFFFF_FFFF, 32'h0000_0001, 4'd7, 32'hFFFF_FFFF, 1'b0, 1'b0}, // SRA
        '{32'hFFFF_FFFF, 32'h0000_0001, 4'd8, 32'h0000_0001, 1'b0, 1'b0}, // SLT
        '{32'hFFFF_FFFF, 32'h0000_0001, 4'd9, 32'h0000_0000, 1'b1, 1'b0}  // SLTU
    };

    // Additional ALU test vectors for edge cases, overflow, negative numbers, and shifts
    const alu_vec_t alu_vectors_ext[] = '{
        // Overflow/underflow
        '{32'h7FFFFFFF, 32'h00000001, 4'd0, 32'h80000000, 1'b0, 1'b1}, // ADD overflow
        '{32'h80000000, 32'hFFFFFFFF, 4'd1, 32'h7FFFFFFF, 1'b0, 1'b1}, // SUB underflow
        // Negative numbers
        '{32'hFFFFFFFF, 32'h00000001, 4'd0, 32'h00000000, 1'b1, 1'b0}, // -1 + 1 = 0
        '{32'hFFFFFFFE, 32'hFFFFFFFE, 4'd0, 32'hFFFFFFFC, 1'b0, 1'b0}, // -2 + -2
        // Bitwise edge cases
        '{32'hAAAAAAAA, 32'h55555555, 4'd2, 32'h00000000, 1'b1, 1'b0}, // AND alternating bits
        '{32'hAAAAAAAA, 32'h55555555, 4'd3, 32'hFFFFFFFF, 1'b0, 1'b0}, // OR alternating bits
        // Shifts
        '{32'h00000001, 32'h0000001F, 4'd5, 32'h80000000, 1'b0, 1'b0}, // SLL by 31
        '{32'h80000000, 32'h0000001F, 4'd6, 32'h00000001, 1'b0, 1'b0}, // SRL by 31
        '{32'h80000000, 32'h0000001F, 4'd7, 32'hFFFFFFFF, 1'b0, 1'b0}, // SRA by 31 (sign extend)
        // SLT/SLTU
        '{32'h00000001, 32'h00000001, 4'd8, 32'h00000000, 1'b1, 1'b0}, // SLT equal
        '{32'h80000000, 32'h00000000, 4'd8, 32'h00000001, 1'b0, 1'b0}, // SLT negative < positive
        '{32'hFFFFFFFF, 32'h00000001, 4'd9, 32'h0000000, 1'b1, 1'b0}   // SLTU unsigned
    };

    //===========================================================================
    // Register File Test Vectors
    //===========================================================================
    typedef struct packed {
        logic [4:0] rs1_addr;
        logic [4:0] rs2_addr;
        logic [4:0] rd_addr;
        logic [31:0] write_data;
        logic write_enable;
        logic [31:0] expected_rs1_data;
        logic [31:0] expected_rs2_data;
    } regfile_vec_t;

    // Example register file test vectors
    const regfile_vec_t regfile_vectors[] = '{
        '{5'd1, 5'd2, 5'd1, 32'h1234_5678, 1'b1, 32'h1234_5678, 32'h0000_0000}, // Write/read x1
        '{5'd0, 5'd0, 5'd0, 32'hDEAD_BEEF, 1'b1, 32'h0000_0000, 32'h0000_0000}, // x0 always zero
        '{5'd3, 5'd4, 5'd3, 32'hABCD_EF01, 1'b1, 32'hABCD_EF01, 32'h0000_0000}  // Write/read x3
    };

    // Additional register file test vectors for simultaneous writes, x0, and reset
    const regfile_vec_t regfile_vectors_ext[] = '{
        // Simultaneous writes (simulate in testbench loop)
        '{5'd10, 5'd11, 5'd10, 32'hAAAA_AAAA, 1'b1, 32'hAAAA_AAAA, 32'h0000_0000},
        '{5'd11, 5'd10, 5'd11, 32'h5555_5555, 1'b1, 32'h5555_5555, 32'hAAAA_AAAA},
        // Write to all registers (simulate in testbench loop)
        '{5'd31, 5'd0, 5'd31, 32'hDEAD_BEEF, 1'b1, 32'hDEAD_BEEF, 32'h0000_0000},
        // Write with write-enable deasserted
        '{5'd12, 5'd0, 5'd12, 32'h1234_5678, 1'b0, 32'h0000_0000, 32'h0000_0000},
        // Read from uninitialized register (should be zero after reset)
        '{5'd13, 5'd0, 5'd0, 32'h0000_0000, 1'b0, 32'h0000_0000, 32'h0000_0000}
    };

    //===========================================================================
    // Memory Test Vectors
    //===========================================================================
    typedef struct packed {
        logic [31:0] addr;
        logic [31:0] write_data;
        logic [2:0] size;
        logic [3:0] strb;
        logic write_enable;
        logic [31:0] expected_read_data;
    } memory_vec_t;

    // Example memory test vectors
    const memory_vec_t memory_vectors[] = '{
        '{32'h0000_1000, 32'hA5A5_A5A5, 3'd2, 4'b1111, 1'b1, 32'hA5A5_A5A5}, // Word write/read
        '{32'h0000_1004, 32'h0000_00FF, 3'd0, 4'b0001, 1'b1, 32'h0000_00FF}, // Byte write/read
        '{32'h0000_1008, 32'h0000_FFFF, 3'd1, 4'b0011, 1'b1, 32'h0000_FFFF}  // Halfword write/read
    };

    // Additional memory test vectors for unaligned, boundary, and burst accesses
    const memory_vec_t memory_vectors_ext[] = '{
        // Unaligned accesses (if supported)
        '{32'h0000_1001, 32'hAABB_CCDD, 3'd0, 4'b0010, 1'b1, 32'h0000_00DD}, // Byte at offset 1
        // Boundary addresses
        '{32'h0000_0FFF, 32'h1234_5678, 3'd2, 4'b1111, 1'b1, 32'h1234_5678}, // End of low region
        '{32'hFFFF_FFFC, 32'h8765_4321, 3'd2, 4'b1111, 1'b1, 32'h8765_4321}, // End of memory
        // Back-to-back write/read
        '{32'h0000_2000, 32'hCAFEBABE, 3'd2, 4'b1111, 1'b1, 32'hCAFEBABE},
        '{32'h0000_2000, 32'h00000000, 3'd2, 4'b1111, 1'b0, 32'hCAFEBABE} // Read after write
    };

    //===========================================================================
    // CSR (Control and Status Register) Test Vectors
    //===========================================================================
    typedef struct packed {
        logic [11:0] csr_addr;
        logic [31:0] write_data;
        logic [1:0] csr_op;
        logic [31:0] expected_read_data;
        logic expected_exception;
    } csr_vec_t;

    const csr_vec_t csr_vectors[] = '{
        // Machine mode CSRs
        '{12'h300, 32'h0000_0001, 2'b01, 32'h0000_0001, 1'b0}, // mstatus
        '{12'h305, 32'h0000_1000, 2'b01, 32'h0000_1000, 1'b0}, // mtvec
        '{12'h341, 32'h0000_0000, 2'b01, 32'h0000_0000, 1'b0}, // mepc
        // Read-only CSRs
        '{12'hF11, 32'h0000_0000, 2'b10, 32'h0000_0000, 1'b0}, // mvendorid
        '{12'hF12, 32'h0000_0000, 2'b10, 32'h0000_0000, 1'b0}, // marchid
        '{12'hF13, 32'h0000_0000, 2'b10, 32'h0000_0000, 1'b0}, // mimpid
        '{12'hF14, 32'h0000_0000, 2'b10, 32'h0000_0000, 1'b0}  // mhartid
    };

    //===========================================================================
    // Exception/Interrupt Test Vectors
    //===========================================================================
    typedef struct packed {
        logic [31:0] pc;
        logic [31:0] instruction;
        logic [3:0] exception_code;
        logic [31:0] expected_handler_pc;
        logic expected_trap;
    } exception_vec_t;

    const exception_vec_t exception_vectors[] = '{
        // Illegal instruction
        '{32'h0000_1000, 32'h0000_0000, 4'd2, 32'h0000_1000, 1'b1}, // Invalid opcode
        // Memory access fault
        '{32'h0000_1004, 32'h0000_2000, 4'd5, 32'h0000_1004, 1'b1}, // Load from invalid addr
        // Environment call
        '{32'h0000_1008, 32'h0000_0073, 4'd11, 32'h0000_1008, 1'b1} // ECALL
    };

    //===========================================================================
    // Pipeline Hazard Test Vectors
    //===========================================================================
    typedef struct packed {
        logic [31:0] inst1;
        logic [31:0] inst2;
        logic [31:0] inst3;
        logic expected_hazard;
        logic [1:0] hazard_type;
    } hazard_vec_t;

    const hazard_vec_t hazard_vectors[] = '{
        // RAW hazard
        '{32'h0010_0093, 32'h0020_8093, 32'h0000_0000, 1'b1, 2'b01}, // add x1, x0, 1; add x1, x1, 2
        // WAW hazard
        '{32'h0010_0093, 32'h0020_0093, 32'h0000_0000, 1'b1, 2'b10}, // add x1, x0, 1; add x1, x0, 2
        // WAR hazard
        '{32'h0010_0093, 32'h0020_8093, 32'h0030_0093, 1'b1, 2'b11}  // add x1, x0, 1; add x1, x1, 2; add x1, x0, 3
    };

    //===========================================================================
    // Branch Prediction Test Vectors
    //===========================================================================
    typedef struct packed {
        logic [31:0] pc;
        logic [31:0] target;
        logic taken;
        logic [1:0] prediction;
        logic misprediction;
    } branch_vec_t;

    const branch_vec_t branch_vectors[] = '{
        // Taken branches
        '{32'h0000_1000, 32'h0000_2000, 1'b1, 2'b01, 1'b0}, // Predict taken, actually taken
        '{32'h0000_1004, 32'h0000_1008, 1'b0, 2'b01, 1'b1}, // Predict taken, actually not taken
        // Not taken branches
        '{32'h0000_1008, 32'h0000_2000, 1'b0, 2'b00, 1'b0}, // Predict not taken, actually not taken
        '{32'h0000_100C, 32'h0000_2000, 1'b1, 2'b00, 1'b1}  // Predict not taken, actually taken
    };

    //===========================================================================
    // Performance Test Vectors (for throughput testing)
    //===========================================================================
    typedef struct packed {
        logic [31:0] instruction_sequence[0:15]; // 16 instructions
        integer expected_cycles;
        integer expected_throughput;
    } performance_vec_t;

    const performance_vec_t performance_vectors[] = '{
        // Ideal throughput (1 IPC)
        '{'{32'h0010_0093, 32'h0020_8093, 32'h0030_0093, 32'h0040_8093,
            32'h0050_0093, 32'h0060_8093, 32'h0070_0093, 32'h0080_8093,
            32'h0090_0093, 32'h00A0_8093, 32'h00B0_0093, 32'h00C0_8093,
            32'h00D0_0093, 32'h00E0_8093, 32'h00F0_0093, 32'h0100_8093}, 16, 1},
        // Hazard-heavy sequence
        '{'{32'h0010_0093, 32'h0020_8093, 32'h0030_0093, 32'h0040_8093,
            32'h0050_0093, 32'h0060_8093, 32'h0070_0093, 32'h0080_8093,
            32'h0090_0093, 32'h00A0_8093, 32'h00B0_0093, 32'h00C0_8093,
            32'h00D0_0093, 32'h00E0_8093, 32'h00F0_0093, 32'h0100_8093}, 20, 0} // Lower throughput due to hazards
    };

    //===========================================================================
    // Cache Test Vectors
    //===========================================================================
    typedef struct packed {
        logic [31:0] addr;
        logic [31:0] data;
        logic [2:0] size;
        logic read_write;
        logic expected_hit;
        logic [1:0] cache_state;
    } cache_vec_t;

    const cache_vec_t cache_vectors[] = '{
        // Cache hit
        '{32'h0000_1000, 32'hA5A5_A5A5, 3'd2, 1'b1, 1'b0, 2'b00}, // First access (miss)
        '{32'h0000_1000, 32'hA5A5_A5A5, 3'd2, 1'b0, 1'b1, 2'b01}, // Second access (hit)
        // Cache miss
        '{32'h0000_2000, 32'hB5B5_B5B5, 3'd2, 1'b1, 1'b0, 2'b00}, // Different address (miss)
        // Cache eviction
        '{32'h0000_3000, 32'hC5C5_C5C5, 3'd2, 1'b1, 1'b0, 2'b10}  // Another address (may cause eviction)
    };

    //===========================================================================
    // AXI4 Protocol Test Vectors
    //===========================================================================
    typedef struct packed {
        logic [31:0] addr;
        logic [31:0] data;
        logic [7:0] len;
        logic [2:0] size;
        logic [1:0] burst;
        logic [3:0] cache;
        logic [2:0] prot;
        logic [3:0] qos;
        logic [3:0] region;
        logic [3:0] user;
    } axi4_vec_t;

    const axi4_vec_t axi4_vectors[] = '{
        // Single transfer
        '{32'h0000_1000, 32'hA5A5_A5A5, 8'd0, 3'd2, 2'b01, 4'b0000, 3'b000, 4'b0000, 4'b0000, 4'b0000},
        // Burst transfer
        '{32'h0000_2000, 32'hB5B5_B5B5, 8'd3, 3'd2, 2'b01, 4'b0000, 3'b000, 4'b0000, 4'b0000, 4'b0000},
        // Cacheable transfer
        '{32'h0000_3000, 32'hC5C5_C5C5, 8'd0, 3'd2, 2'b01, 4'b0011, 3'b000, 4'b0000, 4'b0000, 4'b0000}
    };

    //===========================================================================
    // Random Test Vector Generators
    //===========================================================================
    
    // Function to generate random ALU test vector
    function automatic alu_vec_t random_alu_vector();
        alu_vec_t vec;
        vec.a = $random;
        vec.b = $random;
        vec.op = $random % 10; // 0-9 for ALU operations
        // Calculate expected result based on operation
        case (vec.op)
            4'd0: vec.expected = vec.a + vec.b; // ADD
            4'd1: vec.expected = vec.a - vec.b; // SUB
            4'd2: vec.expected = vec.a & vec.b; // AND
            4'd3: vec.expected = vec.a | vec.b; // OR
            4'd4: vec.expected = vec.a ^ vec.b; // XOR
            4'd5: vec.expected = vec.a << vec.b[4:0]; // SLL
            4'd6: vec.expected = vec.a >> vec.b[4:0]; // SRL
            4'd7: vec.expected = $signed(vec.a) >>> vec.b[4:0]; // SRA
            4'd8: vec.expected = ($signed(vec.a) < $signed(vec.b)) ? 32'd1 : 32'd0; // SLT
            4'd9: vec.expected = (vec.a < vec.b) ? 32'd1 : 32'd0; // SLTU
        endcase
        vec.expected_zero = (vec.expected == 32'h0000_0000);
        vec.expected_overflow = 1'b0; // Simplified - would need proper overflow detection
        return vec;
    endfunction

    // Function to generate random memory test vector
    function automatic memory_vec_t random_memory_vector();
        memory_vec_t vec;
        vec.addr = $random & 32'hFFFF_FFFF;
        vec.write_data = $random;
        vec.size = $random % 4; // 0-3 for byte, halfword, word
        vec.strb = (vec.size == 0) ? (4'b0001 << ($random % 4)) :
                   (vec.size == 1) ? (4'b0011 << (2 * ($random % 2))) : 4'b1111;
        vec.write_enable = $random % 2;
        vec.expected_read_data = vec.write_data;
        return vec;
    endfunction

    // Function to generate random register file test vector
    function automatic regfile_vec_t random_regfile_vector();
        regfile_vec_t vec;
        vec.rs1_addr = $random % 32;
        vec.rs2_addr = $random % 32;
        vec.rd_addr = $random % 32;
        vec.write_data = $random;
        vec.write_enable = $random % 2;
        vec.expected_rs1_data = (vec.rs1_addr == 5'd0) ? 32'h0000_0000 : vec.write_data;
        vec.expected_rs2_data = (vec.rs2_addr == 5'd0) ? 32'h0000_0000 : vec.write_data;
        return vec;
    endfunction

endpackage : test_data

//=============================================================================
// Dependencies: None
//
// Performance: N/A
// Verification Coverage: N/A
// Synthesis: N/A
// Testing: N/A
//
//-----
// Revision History:
// Version | Date       | Author    | Description
//=============================================================================
// 1.0.0   | 2025-06-28 | DesignAI  | Initial release
//============================================================================= 