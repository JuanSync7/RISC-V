//===========================================================================
// File: monitor.sv
// Description: Comprehensive monitor for RISC-V processor verification
// Author: RISC-V Team
// Date: 2024
// Version: 1.0
//===========================================================================

package monitor;

    import test_utils::*;
    import test_data::*;
    import scoreboard::*;

    //===========================================================================
    // Monitor Configuration
    //===========================================================================
    
    // Monitor modes
    typedef enum {
        MONITOR_DISABLED,
        MONITOR_PASSIVE,
        MONITOR_ACTIVE
    } monitor_mode_t;
    
    // Monitor statistics
    typedef struct packed {
        integer total_transactions;
        integer alu_transactions;
        integer memory_transactions;
        integer regfile_transactions;
        integer pipeline_transactions;
        integer exception_transactions;
        time start_time;
        time end_time;
    } monitor_stats_t;
    
    //===========================================================================
    // Monitor Class
    //===========================================================================
    
    class Monitor;
        // Configuration
        monitor_mode_t mode;
        monitor_stats_t stats;
        Scoreboard scoreboard;
        
        // Transaction collection
        alu_transaction_t alu_transactions[$];
        memory_transaction_t memory_transactions[$];
        regfile_transaction_t regfile_transactions[$];
        pipeline_transaction_t pipeline_transactions[$];
        exception_transaction_t exception_transactions[$];
        
        // Constructor
        function new(monitor_mode_t initial_mode = MONITOR_PASSIVE, Scoreboard sb = null);
            mode = initial_mode;
            scoreboard = sb;
            stats.total_transactions = 0;
            stats.alu_transactions = 0;
            stats.memory_transactions = 0;
            stats.regfile_transactions = 0;
            stats.pipeline_transactions = 0;
            stats.exception_transactions = 0;
            stats.start_time = $time;
        endfunction
        
        //===========================================================================
        // ALU Monitor Methods
        //===========================================================================
        
        // Monitor ALU operation
        function void monitor_alu(
            input logic [31:0] operand_a,
            input logic [31:0] operand_b,
            input logic [3:0] operation,
            input logic [31:0] result,
            input logic zero_flag,
            input logic overflow_flag
        );
            if (mode == MONITOR_DISABLED) return;
            
            alu_transaction_t transaction;
            transaction.operand_a = operand_a;
            transaction.operand_b = operand_b;
            transaction.operation = operation;
            transaction.result = result;
            transaction.zero_flag = zero_flag;
            transaction.overflow_flag = overflow_flag;
            transaction.timestamp = $time;
            
            alu_transactions.push_back(transaction);
            stats.alu_transactions++;
            stats.total_transactions++;
            
            // Send to scoreboard if available
            if (scoreboard != null) begin
                scoreboard.add_actual_alu(result, zero_flag, overflow_flag);
            end
            
            // Log transaction if in active mode
            if (mode == MONITOR_ACTIVE) begin
                $display("[%0t] [MONITOR] ALU: op=%0d, a=%h, b=%h, result=%h, zero=%b", 
                         $time, operation, operand_a, operand_b, result, zero_flag);
            end
        endfunction
        
        //===========================================================================
        // Memory Monitor Methods
        //===========================================================================
        
        // Monitor memory read operation
        function void monitor_memory_read(
            input logic [31:0] address,
            input logic [31:0] read_data,
            input logic [2:0] size,
            input logic valid
        );
            if (mode == MONITOR_DISABLED || !valid) return;
            
            memory_transaction_t transaction;
            transaction.address = address;
            transaction.read_data = read_data;
            transaction.size = size;
            transaction.read_write = 1'b0; // Read
            transaction.valid = valid;
            transaction.timestamp = $time;
            
            memory_transactions.push_back(transaction);
            stats.memory_transactions++;
            stats.total_transactions++;
            
            // Send to scoreboard if available
            if (scoreboard != null) begin
                scoreboard.add_actual_memory(address, read_data, size, 1'b0);
            end
            
            // Log transaction if in active mode
            if (mode == MONITOR_ACTIVE) begin
                $display("[%0t] [MONITOR] MEM_READ: addr=%h, data=%h, size=%0d", 
                         $time, address, read_data, size);
            end
        endfunction
        
        // Monitor memory write operation
        function void monitor_memory_write(
            input logic [31:0] address,
            input logic [31:0] write_data,
            input logic [2:0] size,
            input logic [3:0] strb,
            input logic valid
        );
            if (mode == MONITOR_DISABLED || !valid) return;
            
            memory_transaction_t transaction;
            transaction.address = address;
            transaction.write_data = write_data;
            transaction.size = size;
            transaction.strb = strb;
            transaction.read_write = 1'b1; // Write
            transaction.valid = valid;
            transaction.timestamp = $time;
            
            memory_transactions.push_back(transaction);
            stats.memory_transactions++;
            stats.total_transactions++;
            
            // Send to scoreboard if available
            if (scoreboard != null) begin
                scoreboard.add_actual_memory(address, write_data, size, 1'b1);
            end
            
            // Log transaction if in active mode
            if (mode == MONITOR_ACTIVE) begin
                $display("[%0t] [MONITOR] MEM_WRITE: addr=%h, data=%h, size=%0d, strb=%b", 
                         $time, address, write_data, size, strb);
            end
        endfunction
        
        //===========================================================================
        // Register File Monitor Methods
        //===========================================================================
        
        // Monitor register file read operation
        function void monitor_regfile_read(
            input logic [4:0] rs1_addr,
            input logic [4:0] rs2_addr,
            input logic [31:0] rs1_data,
            input logic [31:0] rs2_data
        );
            if (mode == MONITOR_DISABLED) return;
            
            regfile_transaction_t transaction;
            transaction.rs1_addr = rs1_addr;
            transaction.rs2_addr = rs2_addr;
            transaction.rs1_data = rs1_data;
            transaction.rs2_data = rs2_data;
            transaction.timestamp = $time;
            
            regfile_transactions.push_back(transaction);
            stats.regfile_transactions++;
            stats.total_transactions++;
            
            // Send to scoreboard if available
            if (scoreboard != null) begin
                scoreboard.add_actual_regfile(rs1_data, rs2_data);
            end
            
            // Log transaction if in active mode
            if (mode == MONITOR_ACTIVE) begin
                $display("[%0t] [MONITOR] REG_READ: rs1[%0d]=%h, rs2[%0d]=%h", 
                         $time, rs1_addr, rs1_data, rs2_addr, rs2_data);
            end
        endfunction
        
        // Monitor register file write operation
        function void monitor_regfile_write(
            input logic [4:0] rd_addr,
            input logic [31:0] write_data,
            input logic write_enable
        );
            if (mode == MONITOR_DISABLED || !write_enable) return;
            
            // Find the most recent read transaction and update it
            if (regfile_transactions.size() > 0) begin
                regfile_transaction_t transaction = regfile_transactions[$];
                transaction.rd_addr = rd_addr;
                transaction.write_data = write_data;
                transaction.write_enable = write_enable;
                regfile_transactions[$] = transaction;
            end
            
            // Log transaction if in active mode
            if (mode == MONITOR_ACTIVE) begin
                $display("[%0t] [MONITOR] REG_WRITE: rd[%0d]=%h", 
                         $time, rd_addr, write_data);
            end
        endfunction
        
        //===========================================================================
        // Pipeline Monitor Methods
        //===========================================================================
        
        // Monitor pipeline stage
        function void monitor_pipeline_stage(
            input logic [31:0] instruction,
            input logic [31:0] pc,
            input logic [31:0] result,
            input logic valid,
            input logic stall,
            input logic flush,
            input string stage_name
        );
            if (mode == MONITOR_DISABLED) return;
            
            pipeline_transaction_t transaction;
            transaction.instruction = instruction;
            transaction.pc = pc;
            transaction.result = result;
            transaction.valid = valid;
            transaction.stall = stall;
            transaction.flush = flush;
            transaction.timestamp = $time;
            
            pipeline_transactions.push_back(transaction);
            stats.pipeline_transactions++;
            stats.total_transactions++;
            
            // Send to scoreboard if available
            if (scoreboard != null) begin
                scoreboard.add_actual_pipeline(instruction, pc, result, valid, stall, flush);
            end
            
            // Log transaction if in active mode
            if (mode == MONITOR_ACTIVE && valid) begin
                $display("[%0t] [MONITOR] %s: pc=%h, inst=%h, result=%h, stall=%b, flush=%b", 
                         $time, stage_name, pc, instruction, result, stall, flush);
            end
        endfunction
        
        //===========================================================================
        // Exception Monitor Methods
        //===========================================================================
        
        // Monitor exception/interrupt
        function void monitor_exception(
            input logic [3:0] exception_code,
            input logic [31:0] exception_pc,
            input logic [31:0] handler_pc,
            input logic trap_taken
        );
            if (mode == MONITOR_DISABLED) return;
            
            exception_transaction_t transaction;
            transaction.exception_code = exception_code;
            transaction.exception_pc = exception_pc;
            transaction.handler_pc = handler_pc;
            transaction.trap_taken = trap_taken;
            transaction.timestamp = $time;
            
            exception_transactions.push_back(transaction);
            stats.exception_transactions++;
            stats.total_transactions++;
            
            // Send to scoreboard if available
            if (scoreboard != null) begin
                scoreboard.add_actual_exception(exception_code, exception_pc, handler_pc, trap_taken);
            end
            
            // Log transaction if in active mode
            if (mode == MONITOR_ACTIVE) begin
                $display("[%0t] [MONITOR] EXCEPTION: code=%0d, pc=%h, handler=%h, trap=%b", 
                         $time, exception_code, exception_pc, handler_pc, trap_taken);
            end
        endfunction
        
        //===========================================================================
        // Performance Monitor Methods
        //===========================================================================
        
        // Monitor performance metrics
        function void monitor_performance(
            input bit instruction_retired,
            input bit stall,
            input bit flush,
            input bit cache_hit,
            input bit cache_miss
        );
            if (mode == MONITOR_DISABLED) return;
            
            // Update performance statistics
            update_performance_stats(instruction_retired, stall, flush, cache_hit, cache_miss);
            
            // Log performance events if in active mode
            if (mode == MONITOR_ACTIVE) begin
                if (instruction_retired) begin
                    $display("[%0t] [MONITOR] PERFORMANCE: Instruction retired", $time);
                end
                if (stall) begin
                    $display("[%0t] [MONITOR] PERFORMANCE: Pipeline stalled", $time);
                end
                if (flush) begin
                    $display("[%0t] [MONITOR] PERFORMANCE: Pipeline flushed", $time);
                end
                if (cache_hit) begin
                    $display("[%0t] [MONITOR] PERFORMANCE: Cache hit", $time);
                end
                if (cache_miss) begin
                    $display("[%0t] [MONITOR] PERFORMANCE: Cache miss", $time);
                end
            end
        endfunction
        
        //===========================================================================
        // Monitor Utility Methods
        //===========================================================================
        
        // Calculate final statistics
        function void calculate_final_stats();
            stats.end_time = $time;
        endfunction
        
        // Print monitor report
        function void print_monitor_report();
            calculate_final_stats();
            $display("=== MONITOR REPORT ===");
            $display("Total Transactions: %0d", stats.total_transactions);
            $display("ALU Transactions: %0d", stats.alu_transactions);
            $display("Memory Transactions: %0d", stats.memory_transactions);
            $display("Register File Transactions: %0d", stats.regfile_transactions);
            $display("Pipeline Transactions: %0d", stats.pipeline_transactions);
            $display("Exception Transactions: %0d", stats.exception_transactions);
            $display("Simulation Time: %0t", stats.end_time - stats.start_time);
            $display("=====================");
        endfunction
        
        // Get transaction statistics
        function monitor_stats_t get_stats();
            return stats;
        endfunction
        
        // Reset monitor
        function void reset();
            alu_transactions.delete();
            memory_transactions.delete();
            regfile_transactions.delete();
            pipeline_transactions.delete();
            exception_transactions.delete();
            
            stats.total_transactions = 0;
            stats.alu_transactions = 0;
            stats.memory_transactions = 0;
            stats.regfile_transactions = 0;
            stats.pipeline_transactions = 0;
            stats.exception_transactions = 0;
            stats.start_time = $time;
        endfunction
        
        // Set monitor mode
        function void set_mode(monitor_mode_t new_mode);
            mode = new_mode;
        endfunction
        
        // Set scoreboard reference
        function void set_scoreboard(Scoreboard sb);
            scoreboard = sb;
        endfunction
        
        //===========================================================================
        // Transaction Analysis Methods
        //===========================================================================
        
        // Analyze ALU transaction patterns
        function void analyze_alu_patterns();
            integer add_count = 0, sub_count = 0, and_count = 0, or_count = 0, xor_count = 0;
            integer sll_count = 0, srl_count = 0, sra_count = 0, slt_count = 0, sltu_count = 0;
            
            for (int i = 0; i < alu_transactions.size(); i++) begin
                case (alu_transactions[i].operation)
                    4'd0: add_count++;
                    4'd1: sub_count++;
                    4'd2: and_count++;
                    4'd3: or_count++;
                    4'd4: xor_count++;
                    4'd5: sll_count++;
                    4'd6: srl_count++;
                    4'd7: sra_count++;
                    4'd8: slt_count++;
                    4'd9: sltu_count++;
                endcase
            end
            
            $display("=== ALU OPERATION ANALYSIS ===");
            $display("ADD: %0d", add_count);
            $display("SUB: %0d", sub_count);
            $display("AND: %0d", and_count);
            $display("OR:  %0d", or_count);
            $display("XOR: %0d", xor_count);
            $display("SLL: %0d", sll_count);
            $display("SRL: %0d", srl_count);
            $display("SRA: %0d", sra_count);
            $display("SLT: %0d", slt_count);
            $display("SLTU: %0d", sltu_count);
            $display("=============================");
        endfunction
        
        // Analyze memory access patterns
        function void analyze_memory_patterns();
            integer read_count = 0, write_count = 0;
            integer byte_count = 0, halfword_count = 0, word_count = 0;
            
            for (int i = 0; i < memory_transactions.size(); i++) begin
                if (memory_transactions[i].read_write) begin
                    write_count++;
                end else begin
                    read_count++;
                end
                
                case (memory_transactions[i].size)
                    3'd0: byte_count++;
                    3'd1: halfword_count++;
                    3'd2: word_count++;
                endcase
            end
            
            $display("=== MEMORY ACCESS ANALYSIS ===");
            $display("Reads: %0d", read_count);
            $display("Writes: %0d", write_count);
            $display("Byte accesses: %0d", byte_count);
            $display("Halfword accesses: %0d", halfword_count);
            $display("Word accesses: %0d", word_count);
            $display("==============================");
        endfunction
        
        // Analyze pipeline efficiency
        function void analyze_pipeline_efficiency();
            integer valid_count = 0, stall_count = 0, flush_count = 0;
            
            for (int i = 0; i < pipeline_transactions.size(); i++) begin
                if (pipeline_transactions[i].valid) valid_count++;
                if (pipeline_transactions[i].stall) stall_count++;
                if (pipeline_transactions[i].flush) flush_count++;
            end
            
            real efficiency = (valid_count > 0) ? 
                (real'(valid_count) / real'(pipeline_transactions.size())) * 100.0 : 0.0;
            
            $display("=== PIPELINE EFFICIENCY ANALYSIS ===");
            $display("Valid cycles: %0d", valid_count);
            $display("Stall cycles: %0d", stall_count);
            $display("Flush cycles: %0d", flush_count);
            $display("Total cycles: %0d", pipeline_transactions.size());
            $display("Efficiency: %0.2f%%", efficiency);
            $display("====================================");
        endfunction
        
    endclass

endpackage : monitor 