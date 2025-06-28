//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-06-28
//
// File: coverage.sv
// Module: coverage
//
// Project Name: RISC-V RV32IM Core
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
//
// Description:
//   Common coverage groups and macros for all testbenches.
//   Includes ALU, register file, and memory coverage. Extend as needed.
//=============================================================================

package coverage;
    //===========================================================================
    // ALU Operation Coverage
    //===========================================================================
    covergroup alu_op_cg @(posedge clk);
        cp_op: coverpoint alu_op {
            bins add = {4'd0};
            bins sub = {4'd1};
            bins and_op = {4'd2};
            bins or_op = {4'd3};
            bins xor_op = {4'd4};
            bins sll = {4'd5};
            bins srl = {4'd6};
            bins sra = {4'd7};
            bins slt = {4'd8};
            bins sltu = {4'd9};
        }
        zero_cp: coverpoint zero_o;
        overflow_cp: coverpoint overflow_o;
        alu_op_zero_cross: cross cp_op, zero_cp;
        alu_op_overflow_cross: cross cp_op, overflow_cp;
    endgroup

    //===========================================================================
    // Register File Access Coverage
    //===========================================================================
    covergroup regfile_access_cg @(posedge clk);
        rs1_addr_cp: coverpoint rs1_addr_i {
            bins zero_reg = {5'd0};
            bins other_regs = {[5'd1:5'd31]};
        }
        rs2_addr_cp: coverpoint rs2_addr_i {
            bins zero_reg = {5'd0};
            bins other_regs = {[5'd1:5'd31]};
        }
        rd_addr_cp: coverpoint rd_addr_i {
            bins zero_reg = {5'd0};
            bins other_regs = {[5'd1:5'd31]};
        }
        write_en_cp: coverpoint rd_write_en_i;
        rs1_rs2_cross: cross rs1_addr_cp, rs2_addr_cp;
        rd_addr_write_cross: cross rd_addr_cp, write_en_cp;
    endgroup

    //===========================================================================
    // Memory Access Coverage
    //===========================================================================
    covergroup memory_access_cg @(posedge clk);
        addr_cp: coverpoint addr {
            bins low = {[32'h0000_0000:32'h0000_0FFF]};
            bins mid = {[32'h0000_1000:32'h0000_1FFF]};
            bins high = {[32'h0000_2000:32'hFFFF_FFFF]};
        }
        size_cp: coverpoint size {
            bins byte = {3'd0};
            bins halfword = {3'd1};
            bins word = {3'd2};
        }
        write_en_cp: coverpoint write_enable;
        addr_size_cross: cross addr_cp, size_cp;
    endgroup

    //===========================================================================
    // Burst/Sequence Coverage (for memory, if supported)
    //===========================================================================
    covergroup memory_burst_cg @(posedge clk);
        burst_len_cp: coverpoint burst_len {
            bins single = {1};
            bins burst4 = {4};
            bins burst8 = {8};
        }
        burst_type_cp: coverpoint burst_type {
            bins incr = {0};
            bins wrap = {1};
        }
        burst_cross: cross burst_len_cp, burst_type_cp;
    endgroup

    //===========================================================================
    // One-hot Coverage Example (for control signals)
    //===========================================================================
    covergroup one_hot_cg @(posedge clk);
        one_hot_cp: coverpoint ctrl_vector {
            bins one_hot[] = {1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768};
        }
    endgroup

    //===========================================================================
    // CSR Operation Coverage
    //===========================================================================
    covergroup csr_op_cg @(posedge clk);
        csr_addr_cp: coverpoint csr_addr {
            bins machine_mode = {[12'h300:12'h3FF]};
            bins supervisor_mode = {[12'h100:12'h1FF]};
            bins user_mode = {[12'h000:12'h0FF]};
            bins read_only = {[12'hF11:12'hF14]};
        }
        csr_op_cp: coverpoint csr_op {
            bins read = {2'b10};
            bins write = {2'b01};
            bins read_write = {2'b11};
            bins read_set = {2'b10};
            bins read_clear = {2'b10};
        }
        exception_cp: coverpoint csr_exception;
        csr_addr_op_cross: cross csr_addr_cp, csr_op_cp;
        csr_op_exception_cross: cross csr_op_cp, exception_cp;
    endgroup

    //===========================================================================
    // Exception/Interrupt Coverage
    //===========================================================================
    covergroup exception_cg @(posedge clk);
        exception_code_cp: coverpoint exception_code {
            bins instruction_misaligned = {4'd0};
            bins instruction_access_fault = {4'd1};
            bins illegal_instruction = {4'd2};
            bins breakpoint = {4'd3};
            bins load_misaligned = {4'd4};
            bins load_access_fault = {4'd5};
            bins store_misaligned = {4'd6};
            bins store_access_fault = {4'd7};
            bins ecall = {4'd11};
            bins ebreak = {4'd3};
        }
        trap_taken_cp: coverpoint trap_taken;
        handler_pc_cp: coverpoint handler_pc {
            bins low_range = {[32'h0000_0000:32'h0000_0FFF]};
            bins mid_range = {[32'h0000_1000:32'h0000_1FFF]};
            bins high_range = {[32'h0000_2000:32'hFFFF_FFFF]};
        }
        exception_trap_cross: cross exception_code_cp, trap_taken_cp;
    endgroup

    //===========================================================================
    // Pipeline Hazard Coverage
    //===========================================================================
    covergroup hazard_cg @(posedge clk);
        hazard_type_cp: coverpoint hazard_type {
            bins raw_hazard = {2'b01};
            bins waw_hazard = {2'b10};
            bins war_hazard = {2'b11};
            bins no_hazard = {2'b00};
        }
        stall_cp: coverpoint stall;
        flush_cp: coverpoint flush;
        hazard_stall_cross: cross hazard_type_cp, stall_cp;
        hazard_flush_cross: cross hazard_type_cp, flush_cp;
    endgroup

    //===========================================================================
    // Branch Prediction Coverage
    //===========================================================================
    covergroup branch_prediction_cg @(posedge clk);
        prediction_cp: coverpoint prediction {
            bins not_taken = {2'b00};
            bins taken = {2'b01};
            bins weakly_not_taken = {2'b10};
            bins weakly_taken = {2'b11};
        }
        actual_taken_cp: coverpoint actual_taken;
        misprediction_cp: coverpoint misprediction;
        prediction_actual_cross: cross prediction_cp, actual_taken_cp;
        prediction_misprediction_cross: cross prediction_cp, misprediction_cp;
    endgroup

    //===========================================================================
    // Performance Monitoring Coverage
    //===========================================================================
    covergroup performance_cg @(posedge clk);
        throughput_cp: coverpoint throughput {
            bins low = {[0.0:0.3]};
            bins medium = {[0.3:0.7]};
            bins high = {[0.7:1.0]};
        }
        cpi_cp: coverpoint cycles_per_instruction {
            bins ideal = {1};
            bins good = {[1:2]};
            bins poor = {[2:5]};
            bins very_poor = {[5:10]};
        }
        instruction_count_cp: coverpoint instruction_count {
            bins few = {[0:100]};
            bins many = {[100:1000]};
            bins lots = {[1000:10000]};
        }
        throughput_cpi_cross: cross throughput_cp, cpi_cp;
    endgroup

    //===========================================================================
    // Cache Behavior Coverage
    //===========================================================================
    covergroup cache_cg @(posedge clk);
        cache_hit_cp: coverpoint cache_hit;
        cache_miss_cp: coverpoint cache_miss;
        cache_eviction_cp: coverpoint cache_eviction;
        cache_state_cp: coverpoint cache_state {
            bins invalid = {2'b00};
            bins valid = {2'b01};
            bins dirty = {2'b10};
            bins shared = {2'b11};
        }
        cache_hit_miss_cross: cross cache_hit_cp, cache_miss_cp;
        cache_state_eviction_cross: cross cache_state_cp, cache_eviction_cp;
    endgroup

    //===========================================================================
    // AXI4 Protocol Coverage
    //===========================================================================
    covergroup axi4_cg @(posedge clk);
        burst_type_cp: coverpoint burst_type {
            bins fixed = {2'b00};
            bins incr = {2'b01};
            bins wrap = {2'b10};
        }
        burst_len_cp: coverpoint burst_len {
            bins single = {0};
            bins burst4 = {3};
            bins burst8 = {7};
            bins burst16 = {15};
        }
        cache_type_cp: coverpoint cache_type {
            bins device_non_bufferable = {4'b0000};
            bins device_bufferable = {4'b0001};
            bins normal_non_cacheable = {4'b0010};
            bins normal_cacheable = {4'b0011};
        }
        response_cp: coverpoint response {
            bins okay = {2'b00};
            bins exclusive_okay = {2'b01};
            bins slave_error = {2'b10};
            bins decode_error = {2'b11};
        }
        burst_type_len_cross: cross burst_type_cp, burst_len_cp;
        cache_response_cross: cross cache_type_cp, response_cp;
    endgroup

    //===========================================================================
    // Memory Access Pattern Coverage
    //===========================================================================
    covergroup memory_pattern_cg @(posedge clk);
        access_type_cp: coverpoint access_type {
            bins sequential = {2'b00};
            bins random = {2'b01};
            bins burst = {2'b10};
            bins strided = {2'b11};
        }
        access_size_cp: coverpoint access_size {
            bins byte = {0};
            bins halfword = {1};
            bins word = {2};
            bins doubleword = {3};
        }
        alignment_cp: coverpoint alignment {
            bins aligned = {1'b0};
            bins misaligned = {1'b1};
        }
        access_type_size_cross: cross access_type_cp, access_size_cp;
        access_size_alignment_cross: cross access_size_cp, alignment_cp;
    endgroup

    //===========================================================================
    // Power Management Coverage
    //===========================================================================
    covergroup power_cg @(posedge clk);
        power_state_cp: coverpoint power_state {
            bins active = {2'b00};
            bins idle = {2'b01};
            bins sleep = {2'b10};
            bins deep_sleep = {2'b11};
        }
        clock_enable_cp: coverpoint clock_enable;
        power_gate_cp: coverpoint power_gate;
        power_state_clock_cross: cross power_state_cp, clock_enable_cp;
    endgroup

    //===========================================================================
    // Security Coverage
    //===========================================================================
    covergroup security_cg @(posedge clk);
        privilege_level_cp: coverpoint privilege_level {
            bins user = {2'b00};
            bins supervisor = {2'b01};
            bins machine = {2'b11};
        }
        access_allowed_cp: coverpoint access_allowed;
        security_violation_cp: coverpoint security_violation;
        privilege_access_cross: cross privilege_level_cp, access_allowed_cp;
        privilege_violation_cross: cross privilege_level_cp, security_violation_cp;
    endgroup

    //===========================================================================
    // Coverage Macros for Easy Instantiation
    //===========================================================================
    `define INSTANTIATE_ALU_CG(inst) coverage::alu_op_cg inst = new();
    `define INSTANTIATE_REGFILE_CG(inst) coverage::regfile_access_cg inst = new();
    `define INSTANTIATE_MEMORY_CG(inst) coverage::memory_access_cg inst = new();
    `define INSTANTIATE_MEMORY_BURST_CG(inst) coverage::memory_burst_cg inst = new();
    `define INSTANTIATE_ONE_HOT_CG(inst) coverage::one_hot_cg inst = new();
    `define INSTANTIATE_CSR_CG(inst) coverage::csr_op_cg inst = new();
    `define INSTANTIATE_EXCEPTION_CG(inst) coverage::exception_cg inst = new();
    `define INSTANTIATE_HAZARD_CG(inst) coverage::hazard_cg inst = new();
    `define INSTANTIATE_BRANCH_PREDICTION_CG(inst) coverage::branch_prediction_cg inst = new();
    `define INSTANTIATE_PERFORMANCE_CG(inst) coverage::performance_cg inst = new();
    `define INSTANTIATE_CACHE_CG(inst) coverage::cache_cg inst = new();
    `define INSTANTIATE_AXI4_CG(inst) coverage::axi4_cg inst = new();
    `define INSTANTIATE_MEMORY_PATTERN_CG(inst) coverage::memory_pattern_cg inst = new();
    `define INSTANTIATE_POWER_CG(inst) coverage::power_cg inst = new();
    `define INSTANTIATE_SECURITY_CG(inst) coverage::security_cg inst = new();

    //===========================================================================
    // Coverage Sampling Functions
    //===========================================================================
    
    // Function to sample all coverage groups at once
    function automatic void sample_all_coverage();
        // This function would be called periodically to sample all coverage
        // Implementation depends on specific coverage group instances
    endfunction

    // Function to generate coverage report
    function automatic void generate_coverage_report();
        // This function would generate a comprehensive coverage report
        // Implementation depends on simulator capabilities
    endfunction

    // Function to check coverage goals
    function automatic bit check_coverage_goals();
        // This function would check if coverage goals have been met
        // Returns 1 if all goals met, 0 otherwise
        return 1'b1; // Placeholder
    endfunction
endpackage : coverage

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