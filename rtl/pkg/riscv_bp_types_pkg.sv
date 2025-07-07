//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: riscv_bp_types_pkg.sv
// Module: riscv_bp_types_pkg
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
//
// Description:
//   Contains all shared parameters, data types, and enumerations related to
//   branch prediction. This includes BTB, BHT, and tournament predictor
//   structures and parameters.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_bp_types_pkg;

    import riscv_config_pkg::*;
    import riscv_types_pkg::*;

    //---------------------------------------------------------------------------
    // 1. Branch Predictor Configuration Parameters (now from config package)
    //---------------------------------------------------------------------------
    // All branch predictor parameters are now imported from riscv_config_pkg:
    // DEFAULT_BTB_ENTRIES, DEFAULT_BHT_ENTRIES, DEFAULT_PHT_ENTRIES
    // DEFAULT_SELECTOR_ENTRIES, DEFAULT_GLOBAL_HISTORY_WIDTH, DEFAULT_RSB_ENTRIES
    // BTB_COUNTER_WIDTH, BHT_COUNTER_WIDTH, PHT_COUNTER_WIDTH, SELECTOR_COUNTER_WIDTH, CONFIDENCE_WIDTH

    //---------------------------------------------------------------------------
    // 2. Branch Target Buffer (BTB) Structures
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic        valid;      // Valid bit for this entry
        addr_t       tag;        // PC tag for matching
        addr_t       target;     // Branch target address
        logic [BTB_COUNTER_WIDTH-1:0] counter;    // 2-bit saturating counter
        logic        is_branch;  // Indicates if this is a branch instruction
    } btb_entry_t;

    //---------------------------------------------------------------------------
    // 3. Branch History Table (BHT) Structures
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic [BHT_COUNTER_WIDTH-1:0] counter;    // 2-bit saturating counter
        logic        valid;      // Valid bit
    } bht_entry_t;

    //---------------------------------------------------------------------------
    // 4. Pattern History Table (PHT) Structures
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic [PHT_COUNTER_WIDTH-1:0] counter;    // 2-bit saturating counter
        logic        valid;      // Valid bit
    } pht_entry_t;

    //---------------------------------------------------------------------------
    // 5. Tournament Predictor Selector Table
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic [SELECTOR_COUNTER_WIDTH-1:0] counter; // 2-bit saturating counter
        logic        valid;      // Valid bit
    } selector_entry_t;

    //---------------------------------------------------------------------------
    // 6. Return Stack Buffer (RSB) Structures
    //---------------------------------------------------------------------------
    typedef struct packed {
        addr_t       return_addr; // Return address
        logic        valid;       // Valid bit
    } rsb_entry_t;

    //---------------------------------------------------------------------------
    // 7. Global History Register
    //---------------------------------------------------------------------------
    typedef logic [DEFAULT_GLOBAL_HISTORY_WIDTH-1:0] global_history_t;

    //---------------------------------------------------------------------------
    // 8. Branch Prediction Result
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic        taken;       // Prediction: taken or not taken
        addr_t       target;      // Predicted target address
        logic        btb_hit;     // BTB hit indicator
        logic        bht_hit;     // BHT hit indicator
        logic        pht_hit;     // PHT hit indicator
        logic        rsb_hit;     // RSB hit indicator
        addr_t       ras_target;  // Predicted return address from RAS
        logic [CONFIDENCE_WIDTH-1:0] confidence; // Prediction confidence
    } branch_prediction_t;

    //---------------------------------------------------------------------------
    // 9. Branch Update Information
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic        valid;       // Update is valid
        addr_t       pc;          // Branch PC
        addr_t       target;      // Actual target
        logic        taken;       // Actual outcome
        logic        is_branch;   // Is this a branch instruction
        logic        is_return;   // Is this a return instruction
        logic        is_call;     // Is this a call instruction
        logic        mispredicted; // Was prediction wrong
    } branch_update_t;

    //---------------------------------------------------------------------------
    // 10. Branch Predictor State Machine
    //---------------------------------------------------------------------------
    typedef enum logic [1:0] {
        BP_IDLE,        // Idle state
        BP_LOOKUP,      // Performing lookup
        BP_UPDATE,      // Updating predictors
        BP_FLUSH        // Flushing predictors
    } bp_state_e;

    //---------------------------------------------------------------------------
    // 11. Branch Instruction Types
    //---------------------------------------------------------------------------
    typedef enum logic [2:0] {
        BRANCH_TYPE_NONE,
        BRANCH_TYPE_CONDITIONAL,  // beq, bne, blt, etc.
        BRANCH_TYPE_UNCONDITIONAL, // j, jal
        BRANCH_TYPE_CALL,         // jal
        BRANCH_TYPE_RETURN,       // ret (jalr with ra)
        BRANCH_TYPE_INDIRECT      // jalr
    } branch_type_e;

    //---------------------------------------------------------------------------
    // 12. Branch Predictor Types
    //---------------------------------------------------------------------------
    typedef enum logic [1:0] {
        PREDICTOR_SIMPLE,     // Simple static predictor
        PREDICTOR_BHT,        // Branch History Table
        PREDICTOR_GLOBAL,     // Global History Predictor
        PREDICTOR_TOURNAMENT  // Tournament Predictor
    } predictor_type_e;

    //---------------------------------------------------------------------------
    // 13. Branch Predictor Performance Counters
    //---------------------------------------------------------------------------
    typedef struct packed {
        logic [31:0] total_branches;
        logic [31:0] correct_predictions;
        logic [31:0] mispredictions;
        logic [31:0] btb_hits;
        logic [31:0] btb_misses;
        logic [31:0] bht_hits;
        logic [31:0] bht_misses;
        logic [31:0] pht_hits;
        logic [31:0] pht_misses;
        logic [31:0] rsb_hits;
        logic [31:0] rsb_misses;
    } bp_perf_counters_t;

    //---------------------------------------------------------------------------
    // 14. Branch Predictor Configuration
    //---------------------------------------------------------------------------
    typedef struct packed {
        integer btb_entries;
        integer bht_entries;
        integer pht_entries;
        integer selector_entries;
        integer global_history_width;
        integer rsb_entries;
        predictor_type_e predictor_type;
    } bp_config_t;

    //---------------------------------------------------------------------------
    // 15. Branch Predictor Functions
    //---------------------------------------------------------------------------
    function automatic logic [31:0] calculate_btb_index(
        input addr_t pc,
        input integer btb_entries
    );
        return pc[$clog2(btb_entries)-1:2]; // PC[2] is word-aligned
    endfunction

    function automatic logic [31:0] calculate_bht_index(
        input addr_t pc,
        input global_history_t global_history,
        input integer bht_entries
    );
        return (pc[$clog2(bht_entries)-1:2] ^ global_history) % bht_entries;
    endfunction

    function automatic logic [31:0] calculate_pht_index(
        input global_history_t global_history,
        input integer pht_entries
    );
        return global_history % pht_entries;
    endfunction

    function automatic logic [31:0] calculate_selector_index(
        input addr_t pc,
        input global_history_t global_history,
        input integer selector_entries
    );
        return (pc[$clog2(selector_entries)-1:2] ^ global_history) % selector_entries;
    endfunction

    function automatic branch_type_e classify_branch(
        input word_t instruction
    );
        logic [6:0] opcode;
        logic [2:0] funct3;
        logic [4:0] rd;
        
        opcode = instruction[6:0];
        funct3 = instruction[14:12];
        rd = instruction[11:7];
        
        case (opcode)
            OPCODE_BRANCH: return BRANCH_TYPE_CONDITIONAL;
            OPCODE_JAL: begin
                if (rd == 5'h01) return BRANCH_TYPE_CALL; // jal ra, target
                else return BRANCH_TYPE_UNCONDITIONAL;
            end
            OPCODE_JALR: begin
                if (rd == 5'h01 && funct3 == 3'b000) return BRANCH_TYPE_RETURN; // jalr ra, rs1, 0
                else return BRANCH_TYPE_INDIRECT;
            end
            default: return BRANCH_TYPE_NONE;
        endcase
    endfunction

    function automatic logic is_branch_instruction(input word_t instruction);
        logic [6:0] opcode;
        opcode = instruction[6:0];
        return (opcode == OPCODE_BRANCH) || (opcode == OPCODE_JAL) || (opcode == OPCODE_JALR);
    endfunction

    function automatic logic is_return_instruction(input word_t instruction);
        logic [6:0] opcode;
        logic [2:0] funct3;
        logic [4:0] rd;
        
        opcode = instruction[6:0];
        funct3 = instruction[14:12];
        rd = instruction[11:7];
        
        return (opcode == OPCODE_JALR) && (rd == 5'h01) && (funct3 == 3'b000);
    endfunction

    function automatic logic is_call_instruction(input word_t instruction);
        logic [6:0] opcode;
        logic [4:0] rd;
        
        opcode = instruction[6:0];
        rd = instruction[11:7];
        
        return (opcode == OPCODE_JAL) && (rd == 5'h01);
    endfunction

endpackage : riscv_bp_types_pkg 