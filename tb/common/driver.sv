//===========================================================================
// File: driver.sv
// Description: Comprehensive driver for RISC-V processor verification
// Author: RISC-V Team
// Date: 2024
// Version: 1.0
//===========================================================================

package driver;

    import test_utils::*;
    import test_data::*;
    import scoreboard::*;
    import monitor::*;

    //===========================================================================
    // Driver Configuration
    //===========================================================================
    
    // Driver modes
    typedef enum {
        DRIVER_DISABLED,
        DRIVER_BASIC,
        DRIVER_ADVANCED,
        DRIVER_STRESS
    } driver_mode_t;
    
    // Driver statistics
    typedef struct packed {
        integer total_stimuli;
        integer alu_stimuli;
        integer memory_stimuli;
        integer regfile_stimuli;
        integer pipeline_stimuli;
        integer exception_stimuli;
        time start_time;
        time end_time;
    } driver_stats_t;
    
    //===========================================================================
    // Driver Class
    //===========================================================================
    
    class Driver;
        // Configuration
        driver_mode_t mode;
        driver_stats_t stats;
        Scoreboard scoreboard;
        Monitor monitor;
        
        // Stimulus generation
        integer stimulus_count;
        integer max_stimuli;
        bit stimulus_complete;
        
        // Constructor
        function new(
            driver_mode_t initial_mode = DRIVER_BASIC,
            Scoreboard sb = null,
            Monitor mon = null
        );
            mode = initial_mode;
            scoreboard = sb;
            monitor = mon;
            stats.total_stimuli = 0;
            stats.alu_stimuli = 0;
            stats.memory_stimuli = 0;
            stats.regfile_stimuli = 0;
            stats.pipeline_stimuli = 0;
            stats.exception_stimuli = 0;
            stats.start_time = $time;
            stimulus_count = 0;
            max_stimuli = 1000;
            stimulus_complete = 1'b0;
        endfunction
        
        //===========================================================================
        // ALU Driver Methods
        //===========================================================================
        
        // Generate ALU stimulus
        function void generate_alu_stimulus();
            if (mode == DRIVER_DISABLED) return;
            
            logic [31:0] operand_a, operand_b;
            logic [3:0] operation;
            
            // Generate random operands
            operand_a = $random;
            operand_b = $random;
            operation = $random % 10; // 0-9 for ALU operations
            
            // Send expected result to scoreboard
            if (scoreboard != null) begin
                scoreboard.add_expected_alu(operand_a, operand_b, operation);
            end
            
            // Apply stimulus to DUT (placeholder)
            apply_alu_stimulus(operand_a, operand_b, operation);
            
            stats.alu_stimuli++;
            stats.total_stimuli++;
            stimulus_count++;
            
            // Log stimulus if in advanced mode
            if (mode == DRIVER_ADVANCED || mode == DRIVER_STRESS) begin
                $display("[%0t] [DRIVER] ALU Stimulus: op=%0d, a=%h, b=%h", 
                         $time, operation, operand_a, operand_b);
            end
        endfunction
        
        // Apply ALU stimulus to DUT
        function void apply_alu_stimulus(
            input logic [31:0] a,
            input logic [31:0] b,
            input logic [3:0] op
        );
            // This function would apply the stimulus to the actual DUT
            // Implementation depends on the specific DUT interface
            // For now, this is a placeholder
        endfunction
        
        // Generate comprehensive ALU test sequence
        function void generate_alu_test_sequence();
            if (mode == DRIVER_DISABLED) return;
            
            // Test all ALU operations with edge cases
            for (int op = 0; op < 10; op++) begin
                // Test with zero operands
                generate_alu_stimulus_with_operands(32'h0000_0000, 32'h0000_0000, op);
                
                // Test with maximum values
                generate_alu_stimulus_with_operands(32'hFFFF_FFFF, 32'hFFFF_FFFF, op);
                
                // Test with mixed values
                generate_alu_stimulus_with_operands(32'hA5A5_A5A5, 32'h5A5A_5A5A, op);
                
                // Test with random values
                for (int i = 0; i < 5; i++) begin
                    generate_alu_stimulus_with_operands($random, $random, op);
                end
            end
        endfunction
        
        // Generate ALU stimulus with specific operands
        function void generate_alu_stimulus_with_operands(
            input logic [31:0] a,
            input logic [31:0] b,
            input logic [3:0] op
        );
            // Send expected result to scoreboard
            if (scoreboard != null) begin
                scoreboard.add_expected_alu(a, b, op);
            end
            
            // Apply stimulus to DUT
            apply_alu_stimulus(a, b, op);
            
            stats.alu_stimuli++;
            stats.total_stimuli++;
            stimulus_count++;
        endfunction
        
        //===========================================================================
        // Memory Driver Methods
        //===========================================================================
        
        // Generate memory stimulus
        function void generate_memory_stimulus();
            if (mode == DRIVER_DISABLED) return;
            
            logic [31:0] address, data;
            logic [2:0] size;
            logic read_write;
            
            // Generate random memory access
            address = $random & 32'hFFFF_FFFF;
            data = $random;
            size = $random % 4; // 0-3 for byte, halfword, word
            read_write = $random % 2;
            
            // Send expected result to scoreboard
            if (scoreboard != null) begin
                scoreboard.add_expected_memory(address, data, size, read_write);
            end
            
            // Apply stimulus to DUT
            apply_memory_stimulus(address, data, size, read_write);
            
            stats.memory_stimuli++;
            stats.total_stimuli++;
            stimulus_count++;
            
            // Log stimulus if in advanced mode
            if (mode == DRIVER_ADVANCED || mode == DRIVER_STRESS) begin
                string access_type = read_write ? "WRITE" : "READ";
                $display("[%0t] [DRIVER] Memory Stimulus: %s addr=%h, data=%h, size=%0d", 
                         $time, access_type, address, data, size);
            end
        endfunction
        
        // Apply memory stimulus to DUT
        function void apply_memory_stimulus(
            input logic [31:0] addr,
            input logic [31:0] data,
            input logic [2:0] size,
            input logic read_write
        );
            // This function would apply the stimulus to the actual DUT
            // Implementation depends on the specific DUT interface
            // For now, this is a placeholder
        endfunction
        
        // Generate memory test patterns
        function void generate_memory_test_patterns();
            if (mode == DRIVER_DISABLED) return;
            
            // Sequential access pattern
            for (int i = 0; i < 100; i++) begin
                logic [31:0] addr = 32'h0000_1000 + (i * 4);
                logic [31:0] data = $random;
                generate_memory_stimulus_with_params(addr, data, 2, 1'b1); // Write word
                generate_memory_stimulus_with_params(addr, 32'h0000_0000, 2, 1'b0); // Read word
            end
            
            // Random access pattern
            for (int i = 0; i < 50; i++) begin
                logic [31:0] addr = $random & 32'hFFFF_FFFF;
                logic [31:0] data = $random;
                logic [2:0] size = $random % 4;
                logic read_write = $random % 2;
                generate_memory_stimulus_with_params(addr, data, size, read_write);
            end
            
            // Burst access pattern
            for (int i = 0; i < 10; i++) begin
                logic [31:0] base_addr = 32'h0000_2000 + (i * 64);
                for (int j = 0; j < 16; j++) begin
                    logic [31:0] addr = base_addr + (j * 4);
                    logic [31:0] data = $random;
                    generate_memory_stimulus_with_params(addr, data, 2, 1'b1); // Write word
                end
            end
        endfunction
        
        // Generate memory stimulus with specific parameters
        function void generate_memory_stimulus_with_params(
            input logic [31:0] addr,
            input logic [31:0] data,
            input logic [2:0] size,
            input logic read_write
        );
            // Send expected result to scoreboard
            if (scoreboard != null) begin
                scoreboard.add_expected_memory(addr, data, size, read_write);
            end
            
            // Apply stimulus to DUT
            apply_memory_stimulus(addr, data, size, read_write);
            
            stats.memory_stimuli++;
            stats.total_stimuli++;
            stimulus_count++;
        endfunction
        
        //===========================================================================
        // Register File Driver Methods
        //===========================================================================
        
        // Generate register file stimulus
        function void generate_regfile_stimulus();
            if (mode == DRIVER_DISABLED) return;
            
            logic [4:0] rs1_addr, rs2_addr, rd_addr;
            logic [31:0] write_data;
            logic write_enable;
            
            // Generate random register access
            rs1_addr = $random % 32;
            rs2_addr = $random % 32;
            rd_addr = $random % 32;
            write_data = $random;
            write_enable = $random % 2;
            
            // Send expected result to scoreboard
            if (scoreboard != null) begin
                scoreboard.add_expected_regfile(rs1_addr, rs2_addr, rd_addr, write_data, write_enable);
            end
            
            // Apply stimulus to DUT
            apply_regfile_stimulus(rs1_addr, rs2_addr, rd_addr, write_data, write_enable);
            
            stats.regfile_stimuli++;
            stats.total_stimuli++;
            stimulus_count++;
            
            // Log stimulus if in advanced mode
            if (mode == DRIVER_ADVANCED || mode == DRIVER_STRESS) begin
                $display("[%0t] [DRIVER] RegFile Stimulus: rs1[%0d], rs2[%0d], rd[%0d]=%h, write=%b", 
                         $time, rs1_addr, rs2_addr, rd_addr, write_data, write_enable);
            end
        endfunction
        
        // Apply register file stimulus to DUT
        function void apply_regfile_stimulus(
            input logic [4:0] rs1_addr,
            input logic [4:0] rs2_addr,
            input logic [4:0] rd_addr,
            input logic [31:0] write_data,
            input logic write_enable
        );
            // This function would apply the stimulus to the actual DUT
            // Implementation depends on the specific DUT interface
            // For now, this is a placeholder
        endfunction
        
        // Generate register file test sequence
        function void generate_regfile_test_sequence();
            if (mode == DRIVER_DISABLED) return;
            
            // Test all registers
            for (int i = 1; i < 32; i++) begin // Skip x0
                logic [31:0] test_data = $random;
                
                // Write to register
                generate_regfile_stimulus_with_params(5'd0, 5'd0, i, test_data, 1'b1);
                
                // Read from register
                generate_regfile_stimulus_with_params(i, 5'd0, 5'd0, 32'h0000_0000, 1'b0);
            end
            
            // Test x0 register (should always read as zero)
            for (int i = 0; i < 10; i++) begin
                generate_regfile_stimulus_with_params(5'd0, 5'd0, 5'd0, 32'h0000_0000, 1'b0);
            end
        endfunction
        
        // Generate register file stimulus with specific parameters
        function void generate_regfile_stimulus_with_params(
            input logic [4:0] rs1_addr,
            input logic [4:0] rs2_addr,
            input logic [4:0] rd_addr,
            input logic [31:0] write_data,
            input logic write_enable
        );
            // Send expected result to scoreboard
            if (scoreboard != null) begin
                scoreboard.add_expected_regfile(rs1_addr, rs2_addr, rd_addr, write_data, write_enable);
            end
            
            // Apply stimulus to DUT
            apply_regfile_stimulus(rs1_addr, rs2_addr, rd_addr, write_data, write_enable);
            
            stats.regfile_stimuli++;
            stats.total_stimuli++;
            stimulus_count++;
        endfunction
        
        //===========================================================================
        // Pipeline Driver Methods
        //===========================================================================
        
        // Generate pipeline stimulus
        function void generate_pipeline_stimulus();
            if (mode == DRIVER_DISABLED) return;
            
            logic [31:0] instruction, pc, result;
            logic valid, stall, flush;
            
            // Generate random pipeline stimulus
            instruction = $random;
            pc = $random & 32'hFFFF_FFFF;
            result = $random;
            valid = $random % 2;
            stall = $random % 2;
            flush = $random % 2;
            
            // Send expected result to scoreboard
            if (scoreboard != null) begin
                scoreboard.add_expected_pipeline(instruction, pc, result);
            end
            
            // Apply stimulus to DUT
            apply_pipeline_stimulus(instruction, pc, result, valid, stall, flush);
            
            stats.pipeline_stimuli++;
            stats.total_stimuli++;
            stimulus_count++;
            
            // Log stimulus if in advanced mode
            if (mode == DRIVER_ADVANCED || mode == DRIVER_STRESS) begin
                $display("[%0t] [DRIVER] Pipeline Stimulus: pc=%h, inst=%h, valid=%b, stall=%b, flush=%b", 
                         $time, pc, instruction, valid, stall, flush);
            end
        endfunction
        
        // Apply pipeline stimulus to DUT
        function void apply_pipeline_stimulus(
            input logic [31:0] instruction,
            input logic [31:0] pc,
            input logic [31:0] result,
            input logic valid,
            input logic stall,
            input logic flush
        );
            // This function would apply the stimulus to the actual DUT
            // Implementation depends on the specific DUT interface
            // For now, this is a placeholder
        endfunction
        
        // Generate instruction sequence
        function void generate_instruction_sequence(integer num_instructions);
            if (mode == DRIVER_DISABLED) return;
            
            logic [31:0] pc = 32'h0000_1000;
            
            for (int i = 0; i < num_instructions; i++) begin
                logic [31:0] instruction = generate_random_instruction();
                
                // Send expected result to scoreboard
                if (scoreboard != null) begin
                    scoreboard.add_expected_pipeline(instruction, pc, 32'h0000_0000);
                end
                
                // Apply stimulus to DUT
                apply_pipeline_stimulus(instruction, pc, 32'h0000_0000, 1'b1, 1'b0, 1'b0);
                
                pc += 4;
                stats.pipeline_stimuli++;
                stats.total_stimuli++;
                stimulus_count++;
            end
        endfunction
        
        // Generate random instruction
        function logic [31:0] generate_random_instruction();
            logic [31:0] instruction;
            logic [6:0] opcode;
            logic [2:0] funct3;
            logic [6:0] funct7;
            
            // Generate random instruction type
            opcode = $random % 128;
            funct3 = $random % 8;
            funct7 = $random % 128;
            
            // Construct instruction based on opcode
            case (opcode)
                7'b0110011: begin // R-type
                    instruction = {funct7, 5'd0, 5'd0, funct3, 5'd0, opcode};
                end
                7'b0010011: begin // I-type
                    instruction = {12'd0, 5'd0, funct3, 5'd0, opcode};
                end
                7'b0100011: begin // S-type
                    instruction = {7'd0, 5'd0, 5'd0, funct3, 5'd0, opcode};
                end
                7'b1100011: begin // B-type
                    instruction = {7'd0, 5'd0, 5'd0, funct3, 5'd0, opcode};
                end
                default: begin
                    instruction = {12'd0, 5'd0, 3'd0, 5'd0, opcode};
                end
            endcase
            
            return instruction;
        endfunction
        
        //===========================================================================
        // Exception Driver Methods
        //===========================================================================
        
        // Generate exception stimulus
        function void generate_exception_stimulus();
            if (mode == DRIVER_DISABLED) return;
            
            logic [3:0] exception_code;
            logic [31:0] exception_pc, handler_pc;
            logic trap_taken;
            
            // Generate random exception
            exception_code = $random % 16;
            exception_pc = $random & 32'hFFFF_FFFF;
            handler_pc = 32'h0000_1000 + (exception_code * 4);
            trap_taken = $random % 2;
            
            // Send expected result to scoreboard
            if (scoreboard != null) begin
                scoreboard.add_expected_exception(exception_code, exception_pc, handler_pc);
            end
            
            // Apply stimulus to DUT
            apply_exception_stimulus(exception_code, exception_pc, handler_pc, trap_taken);
            
            stats.exception_stimuli++;
            stats.total_stimuli++;
            stimulus_count++;
            
            // Log stimulus if in advanced mode
            if (mode == DRIVER_ADVANCED || mode == DRIVER_STRESS) begin
                $display("[%0t] [DRIVER] Exception Stimulus: code=%0d, pc=%h, handler=%h, trap=%b", 
                         $time, exception_code, exception_pc, handler_pc, trap_taken);
            end
        endfunction
        
        // Apply exception stimulus to DUT
        function void apply_exception_stimulus(
            input logic [3:0] exception_code,
            input logic [31:0] exception_pc,
            input logic [31:0] handler_pc,
            input logic trap_taken
        );
            // This function would apply the stimulus to the actual DUT
            // Implementation depends on the specific DUT interface
            // For now, this is a placeholder
        endfunction
        
        //===========================================================================
        // Driver Control Methods
        //===========================================================================
        
        // Run driver
        function void run();
            if (mode == DRIVER_DISABLED) return;
            
            $display("[%0t] [DRIVER] Starting driver in mode %s", $time, get_mode_string());
            
            // Generate comprehensive test sequences
            generate_alu_test_sequence();
            generate_memory_test_patterns();
            generate_regfile_test_sequence();
            generate_instruction_sequence(100);
            
            // Generate random stimuli
            while (stimulus_count < max_stimuli) begin
                case ($random % 5)
                    0: generate_alu_stimulus();
                    1: generate_memory_stimulus();
                    2: generate_regfile_stimulus();
                    3: generate_pipeline_stimulus();
                    4: generate_exception_stimulus();
                endcase
                
                // Add delay between stimuli
                #10;
            end
            
            stimulus_complete = 1'b1;
            $display("[%0t] [DRIVER] Driver completed. Total stimuli: %0d", $time, stats.total_stimuli);
        endfunction
        
        // Get mode string
        function string get_mode_string();
            case (mode)
                DRIVER_DISABLED: return "DISABLED";
                DRIVER_BASIC: return "BASIC";
                DRIVER_ADVANCED: return "ADVANCED";
                DRIVER_STRESS: return "STRESS";
                default: return "UNKNOWN";
            endcase
        endfunction
        
        // Calculate final statistics
        function void calculate_final_stats();
            stats.end_time = $time;
        endfunction
        
        // Print driver report
        function void print_driver_report();
            calculate_final_stats();
            $display("=== DRIVER REPORT ===");
            $display("Mode: %s", get_mode_string());
            $display("Total Stimuli: %0d", stats.total_stimuli);
            $display("ALU Stimuli: %0d", stats.alu_stimuli);
            $display("Memory Stimuli: %0d", stats.memory_stimuli);
            $display("Register File Stimuli: %0d", stats.regfile_stimuli);
            $display("Pipeline Stimuli: %0d", stats.pipeline_stimuli);
            $display("Exception Stimuli: %0d", stats.exception_stimuli);
            $display("Simulation Time: %0t", stats.end_time - stats.start_time);
            $display("====================");
        endfunction
        
        // Reset driver
        function void reset();
            stats.total_stimuli = 0;
            stats.alu_stimuli = 0;
            stats.memory_stimuli = 0;
            stats.regfile_stimuli = 0;
            stats.pipeline_stimuli = 0;
            stats.exception_stimuli = 0;
            stats.start_time = $time;
            stimulus_count = 0;
            stimulus_complete = 1'b0;
        endfunction
        
        // Set driver mode
        function void set_mode(driver_mode_t new_mode);
            mode = new_mode;
        endfunction
        
        // Set maximum stimuli
        function void set_max_stimuli(integer max);
            max_stimuli = max;
        endfunction
        
        // Check if stimulus generation is complete
        function bit is_complete();
            return stimulus_complete;
        endfunction
        
    endclass

endpackage : driver 