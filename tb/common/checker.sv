//===========================================================================
// File: checker.sv
// Description: Comprehensive checker for RISC-V processor verification
// Author: RISC-V Team
// Date: 2024
// Version: 1.0
//===========================================================================

package checker;

    import test_utils::*;
    import test_data::*;
    import assertions::*;

    //===========================================================================
    // Checker Configuration
    //===========================================================================
    
    // Checker modes
    typedef enum {
        CHECKER_DISABLED,
        CHECKER_BASIC,
        CHECKER_STRICT,
        CHECKER_DEBUG
    } checker_mode_t;
    
    // Checker statistics
    typedef struct packed {
        integer total_checks;
        integer passed_checks;
        integer failed_checks;
        integer warnings;
        real pass_rate;
        time start_time;
        time end_time;
    } checker_stats_t;
    
    //===========================================================================
    // Protocol Checker Class
    //===========================================================================
    
    class ProtocolChecker;
        // Configuration
        checker_mode_t mode;
        checker_stats_t stats;
        
        // Constructor
        function new(checker_mode_t initial_mode = CHECKER_BASIC);
            mode = initial_mode;
            stats.total_checks = 0;
            stats.passed_checks = 0;
            stats.failed_checks = 0;
            stats.warnings = 0;
            stats.pass_rate = 0.0;
            stats.start_time = $time;
        endfunction
        
        //===========================================================================
        // AXI4 Protocol Checking
        //===========================================================================
        
        // Check AXI4 write address channel
        function void check_axi4_write_address(
            input logic [31:0] awaddr,
            input logic [7:0] awlen,
            input logic [2:0] awsize,
            input logic [1:0] awburst,
            input logic [3:0] awcache,
            input logic [2:0] awprot,
            input logic awvalid,
            input logic awready
        );
            if (mode == CHECKER_DISABLED) return;
            
            stats.total_checks++;
            
            // Check address alignment
            if (awsize == 3'd0 && awaddr[0] != 1'b0) begin
                log_checker_error("AXI4 write address not byte-aligned");
                stats.failed_checks++;
            end else if (awsize == 3'd1 && awaddr[1:0] != 2'b00) begin
                log_checker_error("AXI4 write address not halfword-aligned");
                stats.failed_checks++;
            end else if (awsize == 3'd2 && awaddr[2:0] != 3'b000) begin
                log_checker_error("AXI4 write address not word-aligned");
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
            
            // Check burst length
            if (awburst == 2'b01 && awlen > 8'd255) begin // INCR burst
                log_checker_error("AXI4 INCR burst length exceeds 255");
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
            
            // Check handshake protocol
            if (awvalid && !awready) begin
                // Valid asserted, ready not yet asserted - this is normal
                stats.passed_checks++;
            end else if (awvalid && awready) begin
                // Handshake completed
                stats.passed_checks++;
            end else begin
                // Invalid state
                log_checker_error("AXI4 write address handshake protocol violation");
                stats.failed_checks++;
            end
        endfunction
        
        // Check AXI4 write data channel
        function void check_axi4_write_data(
            input logic [31:0] wdata,
            input logic [3:0] wstrb,
            input logic wlast,
            input logic wvalid,
            input logic wready
        );
            if (mode == CHECKER_DISABLED) return;
            
            stats.total_checks++;
            
            // Check handshake protocol
            if (wvalid && !wready) begin
                // Valid asserted, ready not yet asserted - this is normal
                stats.passed_checks++;
            end else if (wvalid && wready) begin
                // Handshake completed
                stats.passed_checks++;
            end else begin
                // Invalid state
                log_checker_error("AXI4 write data handshake protocol violation");
                stats.failed_checks++;
            end
            
            // Check write strobe
            if (wstrb == 4'b0000) begin
                log_checker_warning("AXI4 write strobe all zeros - no data written");
                stats.warnings++;
            end else begin
                stats.passed_checks++;
            end
        endfunction
        
        // Check AXI4 write response channel
        function void check_axi4_write_response(
            input logic [1:0] bresp,
            input logic bvalid,
            input logic bready
        );
            if (mode == CHECKER_DISABLED) return;
            
            stats.total_checks++;
            
            // Check response code
            if (bresp == 2'b00) begin
                // OKAY response
                stats.passed_checks++;
            end else if (bresp == 2'b01) begin
                // EXOKAY response
                stats.passed_checks++;
            end else if (bresp == 2'b10) begin
                // SLVERR response
                log_checker_warning("AXI4 slave error response");
                stats.warnings++;
            end else if (bresp == 2'b11) begin
                // DECERR response
                log_checker_error("AXI4 decode error response");
                stats.failed_checks++;
            end
            
            // Check handshake protocol
            if (bvalid && !bready) begin
                // Valid asserted, ready not yet asserted - this is normal
                stats.passed_checks++;
            end else if (bvalid && bready) begin
                // Handshake completed
                stats.passed_checks++;
            end else begin
                // Invalid state
                log_checker_error("AXI4 write response handshake protocol violation");
                stats.failed_checks++;
            end
        endfunction
        
        // Check AXI4 read address channel
        function void check_axi4_read_address(
            input logic [31:0] araddr,
            input logic [7:0] arlen,
            input logic [2:0] arsize,
            input logic [1:0] arburst,
            input logic [3:0] arcache,
            input logic [2:0] arprot,
            input logic arvalid,
            input logic arready
        );
            if (mode == CHECKER_DISABLED) return;
            
            stats.total_checks++;
            
            // Check address alignment
            if (arsize == 3'd0 && araddr[0] != 1'b0) begin
                log_checker_error("AXI4 read address not byte-aligned");
                stats.failed_checks++;
            end else if (arsize == 3'd1 && araddr[1:0] != 2'b00) begin
                log_checker_error("AXI4 read address not halfword-aligned");
                stats.failed_checks++;
            end else if (arsize == 3'd2 && araddr[2:0] != 3'b000) begin
                log_checker_error("AXI4 read address not word-aligned");
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
            
            // Check handshake protocol
            if (arvalid && !arready) begin
                // Valid asserted, ready not yet asserted - this is normal
                stats.passed_checks++;
            end else if (arvalid && arready) begin
                // Handshake completed
                stats.passed_checks++;
            end else begin
                // Invalid state
                log_checker_error("AXI4 read address handshake protocol violation");
                stats.failed_checks++;
            end
        endfunction
        
        // Check AXI4 read data channel
        function void check_axi4_read_data(
            input logic [31:0] rdata,
            input logic [1:0] rresp,
            input logic rlast,
            input logic rvalid,
            input logic rready
        );
            if (mode == CHECKER_DISABLED) return;
            
            stats.total_checks++;
            
            // Check response code
            if (rresp == 2'b00) begin
                // OKAY response
                stats.passed_checks++;
            end else if (rresp == 2'b01) begin
                // EXOKAY response
                stats.passed_checks++;
            end else if (rresp == 2'b10) begin
                // SLVERR response
                log_checker_warning("AXI4 read slave error response");
                stats.warnings++;
            end else if (rresp == 2'b11) begin
                // DECERR response
                log_checker_error("AXI4 read decode error response");
                stats.failed_checks++;
            end
            
            // Check handshake protocol
            if (rvalid && !rready) begin
                // Valid asserted, ready not yet asserted - this is normal
                stats.passed_checks++;
            end else if (rvalid && rready) begin
                // Handshake completed
                stats.passed_checks++;
            end else begin
                // Invalid state
                log_checker_error("AXI4 read data handshake protocol violation");
                stats.failed_checks++;
            end
        endfunction
        
        //===========================================================================
        // Pipeline Protocol Checking
        //===========================================================================
        
        // Check pipeline handshake protocol
        function void check_pipeline_handshake(
            input logic valid_in,
            input logic ready_in,
            input logic valid_out,
            input logic ready_out,
            input string stage_name
        );
            if (mode == CHECKER_DISABLED) return;
            
            stats.total_checks++;
            
            // Check handshake protocol
            if (valid_in && !ready_in) begin
                // Valid asserted, ready not yet asserted - this is normal
                stats.passed_checks++;
            end else if (valid_in && ready_in) begin
                // Handshake completed
                stats.passed_checks++;
            end else if (!valid_in && ready_in) begin
                // Ready asserted, valid not yet asserted - this is normal
                stats.passed_checks++;
            end else begin
                // Invalid state
                log_checker_error($sformatf("Pipeline %s handshake protocol violation", stage_name));
                stats.failed_checks++;
            end
        endfunction
        
        // Check pipeline stall/flush consistency
        function void check_pipeline_control(
            input logic stall,
            input logic flush,
            input logic valid,
            input string stage_name
        );
            if (mode == CHECKER_DISABLED) return;
            
            stats.total_checks++;
            
            // Check that stall and flush are not both active
            if (stall && flush) begin
                log_checker_error($sformatf("Pipeline %s: stall and flush both active", stage_name));
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
            
            // Check that valid is deasserted during flush
            if (flush && valid) begin
                log_checker_error($sformatf("Pipeline %s: valid asserted during flush", stage_name));
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
        endfunction
        
        //===========================================================================
        // Memory Protocol Checking
        //===========================================================================
        
        // Check memory request protocol
        function void check_memory_request(
            input logic [31:0] addr,
            input logic [31:0] data,
            input logic [2:0] size,
            input logic [3:0] strb,
            input logic read_write,
            input logic valid
        );
            if (mode == CHECKER_DISABLED) return;
            
            stats.total_checks++;
            
            // Check address alignment
            if (size == 3'd0 && addr[0] != 1'b0) begin
                log_checker_error("Memory request: byte access not byte-aligned");
                stats.failed_checks++;
            end else if (size == 3'd1 && addr[1:0] != 2'b00) begin
                log_checker_error("Memory request: halfword access not halfword-aligned");
                stats.failed_checks++;
            end else if (size == 3'd2 && addr[2:0] != 3'b000) begin
                log_checker_error("Memory request: word access not word-aligned");
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
            
            // Check write strobe for write operations
            if (read_write && strb == 4'b0000) begin
                log_checker_warning("Memory request: write operation with no strobe bits set");
                stats.warnings++;
            end else begin
                stats.passed_checks++;
            end
        endfunction
        
        // Check memory response protocol
        function void check_memory_response(
            input logic [31:0] data,
            input logic valid,
            input logic error,
            input logic [2:0] size
        );
            if (mode == CHECKER_DISABLED) return;
            
            stats.total_checks++;
            
            // Check that data is valid when response is valid
            if (valid && !error && data === 32'hx) begin
                log_checker_error("Memory response: valid response with X data");
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
            
            // Check error handling
            if (error && valid) begin
                log_checker_warning("Memory response: error response");
                stats.warnings++;
            end else begin
                stats.passed_checks++;
            end
        endfunction
        
        //===========================================================================
        // Register File Protocol Checking
        //===========================================================================
        
        // Check register file read protocol
        function void check_regfile_read(
            input logic [4:0] rs1_addr,
            input logic [4:0] rs2_addr,
            input logic [31:0] rs1_data,
            input logic [31:0] rs2_data
        );
            if (mode == CHECKER_DISABLED) return;
            
            stats.total_checks++;
            
            // Check x0 register always reads as zero
            if (rs1_addr == 5'd0 && rs1_data != 32'h0000_0000) begin
                log_checker_error("Register file: x0 register reads non-zero value");
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
            
            if (rs2_addr == 5'd0 && rs2_data != 32'h0000_0000) begin
                log_checker_error("Register file: x0 register reads non-zero value");
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
            
            // Check that data is not X/Z
            if (rs1_data === 32'hx || rs1_data === 32'hz) begin
                log_checker_error("Register file: rs1 data is X/Z");
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
            
            if (rs2_data === 32'hx || rs2_data === 32'hz) begin
                log_checker_error("Register file: rs2 data is X/Z");
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
        endfunction
        
        // Check register file write protocol
        function void check_regfile_write(
            input logic [4:0] rd_addr,
            input logic [31:0] write_data,
            input logic write_enable
        );
            if (mode == CHECKER_DISABLED) return;
            
            stats.total_checks++;
            
            // Check that x0 register is never written
            if (rd_addr == 5'd0 && write_enable) begin
                log_checker_error("Register file: attempt to write to x0 register");
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
            
            // Check that write data is not X/Z when writing
            if (write_enable && (write_data === 32'hx || write_data === 32'hz)) begin
                log_checker_error("Register file: write data is X/Z");
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
        endfunction
        
        //===========================================================================
        // ALU Protocol Checking
        //===========================================================================
        
        // Check ALU operation protocol
        function void check_alu_operation(
            input logic [31:0] operand_a,
            input logic [31:0] operand_b,
            input logic [3:0] operation,
            input logic [31:0] result,
            input logic zero_flag,
            input logic overflow_flag
        );
            if (mode == CHECKER_DISABLED) return;
            
            stats.total_checks++;
            
            // Check that operands are not X/Z
            if (operand_a === 32'hx || operand_a === 32'hz) begin
                log_checker_error("ALU: operand_a is X/Z");
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
            
            if (operand_b === 32'hx || operand_b === 32'hz) begin
                log_checker_error("ALU: operand_b is X/Z");
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
            
            // Check that result is not X/Z
            if (result === 32'hx || result === 32'hz) begin
                log_checker_error("ALU: result is X/Z");
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
            
            // Check zero flag consistency
            if ((result == 32'h0000_0000) != zero_flag) begin
                log_checker_error("ALU: zero flag inconsistent with result");
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
            
            // Check operation validity
            if (operation > 4'd9) begin
                log_checker_error("ALU: invalid operation code");
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
        endfunction
        
        //===========================================================================
        // Timing Checker Methods
        //===========================================================================
        
        // Check setup time violation
        function void check_setup_time(
            input logic signal,
            input logic clock,
            input time setup_time,
            input string signal_name
        );
            if (mode == CHECKER_DISABLED) return;
            
            stats.total_checks++;
            
            // This is a simplified check - in practice, you would use
            // timing analysis tools or more sophisticated checking
            if (signal === 1'bx || signal === 1'bz) begin
                log_checker_error($sformatf("Timing: %s signal is X/Z", signal_name));
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
        endfunction
        
        // Check hold time violation
        function void check_hold_time(
            input logic signal,
            input logic clock,
            input time hold_time,
            input string signal_name
        );
            if (mode == CHECKER_DISABLED) return;
            
            stats.total_checks++;
            
            // This is a simplified check - in practice, you would use
            // timing analysis tools or more sophisticated checking
            if (signal === 1'bx || signal === 1'bz) begin
                log_checker_error($sformatf("Timing: %s signal is X/Z", signal_name));
                stats.failed_checks++;
            end else begin
                stats.passed_checks++;
            end
        endfunction
        
        //===========================================================================
        // Checker Utility Methods
        //===========================================================================
        
        // Log checker error
        function void log_checker_error(input string message);
            if (mode == CHECKER_DEBUG || mode == CHECKER_STRICT) begin
                $display("[%0t] [CHECKER] ERROR: %s", $time, message);
            end
        endfunction
        
        // Log checker warning
        function void log_checker_warning(input string message);
            if (mode == CHECKER_DEBUG || mode == CHECKER_STRICT) begin
                $display("[%0t] [CHECKER] WARNING: %s", $time, message);
            end
        endfunction
        
        // Calculate final statistics
        function void calculate_final_stats();
            stats.end_time = $time;
            if (stats.total_checks > 0) begin
                stats.pass_rate = real'(stats.passed_checks) / real'(stats.total_checks) * 100.0;
            end
        endfunction
        
        // Print checker report
        function void print_checker_report();
            calculate_final_stats();
            $display("=== CHECKER REPORT ===");
            $display("Total Checks: %0d", stats.total_checks);
            $display("Passed: %0d", stats.passed_checks);
            $display("Failed: %0d", stats.failed_checks);
            $display("Warnings: %0d", stats.warnings);
            $display("Pass Rate: %0.2f%%", stats.pass_rate);
            $display("Simulation Time: %0t", stats.end_time - stats.start_time);
            $display("=====================");
        endfunction
        
        // Reset checker
        function void reset();
            stats.total_checks = 0;
            stats.passed_checks = 0;
            stats.failed_checks = 0;
            stats.warnings = 0;
            stats.pass_rate = 0.0;
            stats.start_time = $time;
        endfunction
        
        // Set checker mode
        function void set_mode(checker_mode_t new_mode);
            mode = new_mode;
        endfunction
        
        // Get checker statistics
        function checker_stats_t get_stats();
            return stats;
        endfunction
        
    endclass

endpackage : checker 