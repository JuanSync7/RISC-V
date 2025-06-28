//===========================================================================
// File: scoreboard.sv
// Description: Comprehensive scoreboard for RISC-V processor verification
// Author: RISC-V Team
// Date: 2024
// Version: 1.0
//===========================================================================

package scoreboard;

    import test_utils::*;
    import test_data::*;

    //===========================================================================
    // Scoreboard Configuration
    //===========================================================================
    
    // Scoreboard modes
    typedef enum {
        SCOREBOARD_DISABLED,
        SCOREBOARD_ENABLED,
        SCOREBOARD_STRICT
    } scoreboard_mode_t;
    
    // Error severity levels
    typedef enum {
        SCOREBOARD_INFO,
        SCOREBOARD_WARNING,
        SCOREBOARD_ERROR,
        SCOREBOARD_FATAL
    } scoreboard_severity_t;
    
    //===========================================================================
    // Transaction Types
    //===========================================================================
    
    // ALU transaction
    typedef struct packed {
        logic [31:0] operand_a;
        logic [31:0] operand_b;
        logic [3:0] operation;
        logic [31:0] result;
        logic zero_flag;
        logic overflow_flag;
        time timestamp;
    } alu_transaction_t;
    
    // Memory transaction
    typedef struct packed {
        logic [31:0] address;
        logic [31:0] write_data;
        logic [31:0] read_data;
        logic [2:0] size;
        logic [3:0] strb;
        logic read_write;
        logic valid;
        time timestamp;
    } memory_transaction_t;
    
    // Register file transaction
    typedef struct packed {
        logic [4:0] rs1_addr;
        logic [4:0] rs2_addr;
        logic [4:0] rd_addr;
        logic [31:0] rs1_data;
        logic [31:0] rs2_data;
        logic [31:0] write_data;
        logic write_enable;
        time timestamp;
    } regfile_transaction_t;
    
    // Pipeline transaction
    typedef struct packed {
        logic [31:0] instruction;
        logic [31:0] pc;
        logic [31:0] result;
        logic valid;
        logic stall;
        logic flush;
        time timestamp;
    } pipeline_transaction_t;
    
    // Exception transaction
    typedef struct packed {
        logic [3:0] exception_code;
        logic [31:0] exception_pc;
        logic [31:0] handler_pc;
        logic trap_taken;
        time timestamp;
    } exception_transaction_t;
    
    //===========================================================================
    // Scoreboard Statistics
    //===========================================================================
    
    typedef struct packed {
        integer total_transactions;
        integer passed_transactions;
        integer failed_transactions;
        integer warnings;
        real pass_rate;
        time start_time;
        time end_time;
    } scoreboard_stats_t;
    
    //===========================================================================
    // Scoreboard Class
    //===========================================================================
    
    class Scoreboard;
        // Configuration
        scoreboard_mode_t mode;
        scoreboard_stats_t stats;
        
        // Transaction queues
        alu_transaction_t alu_expected_queue[$];
        alu_transaction_t alu_actual_queue[$];
        memory_transaction_t memory_expected_queue[$];
        memory_transaction_t memory_actual_queue[$];
        regfile_transaction_t regfile_expected_queue[$];
        regfile_transaction_t regfile_actual_queue[$];
        pipeline_transaction_t pipeline_expected_queue[$];
        pipeline_transaction_t pipeline_actual_queue[$];
        exception_transaction_t exception_expected_queue[$];
        exception_transaction_t exception_actual_queue[$];
        
        // Constructor
        function new(scoreboard_mode_t initial_mode = SCOREBOARD_ENABLED);
            mode = initial_mode;
            stats.total_transactions = 0;
            stats.passed_transactions = 0;
            stats.failed_transactions = 0;
            stats.warnings = 0;
            stats.pass_rate = 0.0;
            stats.start_time = $time;
        endfunction
        
        //===========================================================================
        // ALU Scoreboard Methods
        //===========================================================================
        
        // Add expected ALU transaction
        function void add_expected_alu(
            input logic [31:0] a,
            input logic [31:0] b,
            input logic [3:0] op
        );
            alu_transaction_t expected;
            expected.operand_a = a;
            expected.operand_b = b;
            expected.operation = op;
            expected.timestamp = $time;
            
            // Calculate expected result
            case (op)
                4'd0: expected.result = a + b; // ADD
                4'd1: expected.result = a - b; // SUB
                4'd2: expected.result = a & b; // AND
                4'd3: expected.result = a | b; // OR
                4'd4: expected.result = a ^ b; // XOR
                4'd5: expected.result = a << b[4:0]; // SLL
                4'd6: expected.result = a >> b[4:0]; // SRL
                4'd7: expected.result = $signed(a) >>> b[4:0]; // SRA
                4'd8: expected.result = ($signed(a) < $signed(b)) ? 32'd1 : 32'd0; // SLT
                4'd9: expected.result = (a < b) ? 32'd1 : 32'd0; // SLTU
                default: expected.result = 32'h0000_0000;
            endcase
            
            expected.zero_flag = (expected.result == 32'h0000_0000);
            expected.overflow_flag = 1'b0; // Simplified
            
            alu_expected_queue.push_back(expected);
        endfunction
        
        // Add actual ALU transaction
        function void add_actual_alu(
            input logic [31:0] result,
            input logic zero_flag,
            input logic overflow_flag
        );
            alu_transaction_t actual;
            actual.result = result;
            actual.zero_flag = zero_flag;
            actual.overflow_flag = overflow_flag;
            actual.timestamp = $time;
            
            alu_actual_queue.push_back(actual);
            check_alu_transaction();
        endfunction
        
        // Check ALU transaction
        function void check_alu_transaction();
            if (alu_expected_queue.size() > 0 && alu_actual_queue.size() > 0) begin
                alu_transaction_t expected = alu_expected_queue.pop_front();
                alu_transaction_t actual = alu_actual_queue.pop_front();
                
                stats.total_transactions++;
                
                if (expected.result == actual.result && 
                    expected.zero_flag == actual.zero_flag) begin
                    stats.passed_transactions++;
                    if (mode == SCOREBOARD_STRICT) begin
                        log_scoreboard_message(SCOREBOARD_INFO, 
                            $sformatf("ALU transaction passed: op=%0d, a=%h, b=%h, result=%h", 
                                     expected.operation, expected.operand_a, 
                                     expected.operand_b, actual.result));
                    end
                end else begin
                    stats.failed_transactions++;
                    log_scoreboard_message(SCOREBOARD_ERROR, 
                        $sformatf("ALU transaction failed: op=%0d, a=%h, b=%h, expected=%h, actual=%h", 
                                 expected.operation, expected.operand_a, expected.operand_b, 
                                 expected.result, actual.result));
                end
            end
        endfunction
        
        //===========================================================================
        // Memory Scoreboard Methods
        //===========================================================================
        
        // Add expected memory transaction
        function void add_expected_memory(
            input logic [31:0] addr,
            input logic [31:0] data,
            input logic [2:0] size,
            input logic read_write
        );
            memory_transaction_t expected;
            expected.address = addr;
            expected.write_data = data;
            expected.size = size;
            expected.read_write = read_write;
            expected.timestamp = $time;
            
            memory_expected_queue.push_back(expected);
        endfunction
        
        // Add actual memory transaction
        function void add_actual_memory(
            input logic [31:0] addr,
            input logic [31:0] data,
            input logic [2:0] size,
            input logic read_write
        );
            memory_transaction_t actual;
            actual.address = addr;
            if (read_write) begin
                actual.write_data = data;
            end else begin
                actual.read_data = data;
            end
            actual.size = size;
            actual.read_write = read_write;
            actual.timestamp = $time;
            
            memory_actual_queue.push_back(actual);
            check_memory_transaction();
        endfunction
        
        // Check memory transaction
        function void check_memory_transaction();
            if (memory_expected_queue.size() > 0 && memory_actual_queue.size() > 0) begin
                memory_transaction_t expected = memory_expected_queue.pop_front();
                memory_transaction_t actual = memory_actual_queue.pop_front();
                
                stats.total_transactions++;
                
                if (expected.address == actual.address && 
                    expected.size == actual.size &&
                    expected.read_write == actual.read_write) begin
                    
                    if (expected.read_write) begin
                        // Write transaction - check address and size
                        stats.passed_transactions++;
                    end else begin
                        // Read transaction - check data
                        if (expected.write_data == actual.read_data) begin
                            stats.passed_transactions++;
                        end else begin
                            stats.failed_transactions++;
                            log_scoreboard_message(SCOREBOARD_ERROR, 
                                $sformatf("Memory read failed: addr=%h, expected=%h, actual=%h", 
                                         expected.address, expected.write_data, actual.read_data));
                        end
                    end
                end else begin
                    stats.failed_transactions++;
                    log_scoreboard_message(SCOREBOARD_ERROR, 
                        $sformatf("Memory transaction failed: addr mismatch or protocol error"));
                end
            end
        endfunction
        
        //===========================================================================
        // Register File Scoreboard Methods
        //===========================================================================
        
        // Add expected register file transaction
        function void add_expected_regfile(
            input logic [4:0] rs1_addr,
            input logic [4:0] rs2_addr,
            input logic [4:0] rd_addr,
            input logic [31:0] write_data,
            input logic write_enable
        );
            regfile_transaction_t expected;
            expected.rs1_addr = rs1_addr;
            expected.rs2_addr = rs2_addr;
            expected.rd_addr = rd_addr;
            expected.write_data = write_data;
            expected.write_enable = write_enable;
            expected.timestamp = $time;
            
            // Handle x0 register special case
            if (rs1_addr == 5'd0) expected.rs1_data = 32'h0000_0000;
            if (rs2_addr == 5'd0) expected.rs2_data = 32'h0000_0000;
            
            regfile_expected_queue.push_back(expected);
        endfunction
        
        // Add actual register file transaction
        function void add_actual_regfile(
            input logic [31:0] rs1_data,
            input logic [31:0] rs2_data
        );
            regfile_transaction_t actual;
            actual.rs1_data = rs1_data;
            actual.rs2_data = rs2_data;
            actual.timestamp = $time;
            
            regfile_actual_queue.push_back(actual);
            check_regfile_transaction();
        endfunction
        
        // Check register file transaction
        function void check_regfile_transaction();
            if (regfile_expected_queue.size() > 0 && regfile_actual_queue.size() > 0) begin
                regfile_transaction_t expected = regfile_expected_queue.pop_front();
                regfile_transaction_t actual = regfile_actual_queue.pop_front();
                
                stats.total_transactions++;
                
                bit passed = 1'b1;
                
                // Check x0 register reads
                if (expected.rs1_addr == 5'd0 && actual.rs1_data != 32'h0000_0000) begin
                    passed = 1'b0;
                    log_scoreboard_message(SCOREBOARD_ERROR, 
                        $sformatf("x0 register read failed: expected=0, actual=%h", actual.rs1_data));
                end
                
                if (expected.rs2_addr == 5'd0 && actual.rs2_data != 32'h0000_0000) begin
                    passed = 1'b0;
                    log_scoreboard_message(SCOREBOARD_ERROR, 
                        $sformatf("x0 register read failed: expected=0, actual=%h", actual.rs2_data));
                end
                
                if (passed) begin
                    stats.passed_transactions++;
                end else begin
                    stats.failed_transactions++;
                end
            end
        endfunction
        
        //===========================================================================
        // Pipeline Scoreboard Methods
        //===========================================================================
        
        // Add expected pipeline transaction
        function void add_expected_pipeline(
            input logic [31:0] instruction,
            input logic [31:0] pc,
            input logic [31:0] result
        );
            pipeline_transaction_t expected;
            expected.instruction = instruction;
            expected.pc = pc;
            expected.result = result;
            expected.timestamp = $time;
            
            pipeline_expected_queue.push_back(expected);
        endfunction
        
        // Add actual pipeline transaction
        function void add_actual_pipeline(
            input logic [31:0] instruction,
            input logic [31:0] pc,
            input logic [31:0] result,
            input logic valid,
            input logic stall,
            input logic flush
        );
            pipeline_transaction_t actual;
            actual.instruction = instruction;
            actual.pc = pc;
            actual.result = result;
            actual.valid = valid;
            actual.stall = stall;
            actual.flush = flush;
            actual.timestamp = $time;
            
            pipeline_actual_queue.push_back(actual);
            check_pipeline_transaction();
        endfunction
        
        // Check pipeline transaction
        function void check_pipeline_transaction();
            if (pipeline_expected_queue.size() > 0 && pipeline_actual_queue.size() > 0) begin
                pipeline_transaction_t expected = pipeline_expected_queue.pop_front();
                pipeline_transaction_t actual = pipeline_actual_queue.pop_front();
                
                stats.total_transactions++;
                
                if (actual.valid && !actual.stall && !actual.flush) begin
                    if (expected.instruction == actual.instruction && 
                        expected.pc == actual.pc &&
                        expected.result == actual.result) begin
                        stats.passed_transactions++;
                    end else begin
                        stats.failed_transactions++;
                        log_scoreboard_message(SCOREBOARD_ERROR, 
                            $sformatf("Pipeline transaction failed: instruction mismatch"));
                    end
                end else begin
                    // Pipeline stalled or flushed - this is expected behavior
                    stats.passed_transactions++;
                end
            end
        endfunction
        
        //===========================================================================
        // Exception Scoreboard Methods
        //===========================================================================
        
        // Add expected exception transaction
        function void add_expected_exception(
            input logic [3:0] exception_code,
            input logic [31:0] exception_pc,
            input logic [31:0] handler_pc
        );
            exception_transaction_t expected;
            expected.exception_code = exception_code;
            expected.exception_pc = exception_pc;
            expected.handler_pc = handler_pc;
            expected.trap_taken = 1'b1;
            expected.timestamp = $time;
            
            exception_expected_queue.push_back(expected);
        endfunction
        
        // Add actual exception transaction
        function void add_actual_exception(
            input logic [3:0] exception_code,
            input logic [31:0] exception_pc,
            input logic [31:0] handler_pc,
            input logic trap_taken
        );
            exception_transaction_t actual;
            actual.exception_code = exception_code;
            actual.exception_pc = exception_pc;
            actual.handler_pc = handler_pc;
            actual.trap_taken = trap_taken;
            actual.timestamp = $time;
            
            exception_actual_queue.push_back(actual);
            check_exception_transaction();
        endfunction
        
        // Check exception transaction
        function void check_exception_transaction();
            if (exception_expected_queue.size() > 0 && exception_actual_queue.size() > 0) begin
                exception_transaction_t expected = exception_expected_queue.pop_front();
                exception_transaction_t actual = exception_actual_queue.pop_front();
                
                stats.total_transactions++;
                
                if (expected.exception_code == actual.exception_code &&
                    expected.exception_pc == actual.exception_pc &&
                    expected.handler_pc == actual.handler_pc &&
                    expected.trap_taken == actual.trap_taken) begin
                    stats.passed_transactions++;
                end else begin
                    stats.failed_transactions++;
                    log_scoreboard_message(SCOREBOARD_ERROR, 
                        $sformatf("Exception transaction failed: code=%0d, expected_trap=%b, actual_trap=%b", 
                                 expected.exception_code, expected.trap_taken, actual.trap_taken));
                end
            end
        endfunction
        
        //===========================================================================
        // Scoreboard Utility Methods
        //===========================================================================
        
        // Log scoreboard message
        function void log_scoreboard_message(
            input scoreboard_severity_t severity,
            input string message
        );
            string severity_str;
            case (severity)
                SCOREBOARD_INFO: severity_str = "INFO";
                SCOREBOARD_WARNING: severity_str = "WARNING";
                SCOREBOARD_ERROR: severity_str = "ERROR";
                SCOREBOARD_FATAL: severity_str = "FATAL";
            endcase
            
            $display("[%0t] [SCOREBOARD] [%s] %s", $time, severity_str, message);
            
            if (severity == SCOREBOARD_WARNING) stats.warnings++;
        endfunction
        
        // Calculate final statistics
        function void calculate_final_stats();
            stats.end_time = $time;
            if (stats.total_transactions > 0) begin
                stats.pass_rate = real'(stats.passed_transactions) / real'(stats.total_transactions) * 100.0;
            end
        endfunction
        
        // Print scoreboard report
        function void print_scoreboard_report();
            calculate_final_stats();
            $display("=== SCOREBOARD REPORT ===");
            $display("Total Transactions: %0d", stats.total_transactions);
            $display("Passed: %0d", stats.passed_transactions);
            $display("Failed: %0d", stats.failed_transactions);
            $display("Warnings: %0d", stats.warnings);
            $display("Pass Rate: %0.2f%%", stats.pass_rate);
            $display("Simulation Time: %0t", stats.end_time - stats.start_time);
            $display("========================");
        endfunction
        
        // Reset scoreboard
        function void reset();
            alu_expected_queue.delete();
            alu_actual_queue.delete();
            memory_expected_queue.delete();
            memory_actual_queue.delete();
            regfile_expected_queue.delete();
            regfile_actual_queue.delete();
            pipeline_expected_queue.delete();
            pipeline_actual_queue.delete();
            exception_expected_queue.delete();
            exception_actual_queue.delete();
            
            stats.total_transactions = 0;
            stats.passed_transactions = 0;
            stats.failed_transactions = 0;
            stats.warnings = 0;
            stats.pass_rate = 0.0;
            stats.start_time = $time;
        endfunction
        
    endclass

endpackage : scoreboard 