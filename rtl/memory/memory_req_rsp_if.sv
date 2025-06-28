////////////////////////////////////////////////////////////////////////////////
//
// Company:       Your Company Name
// Engineer:      DesignAI
//
// Create Date:   2025-06-28
// Design Name:   RV32IM Core
// Module Name:   memory_req_rsp_if
// Project Name:  riscv_cpu
// Target Devices:ASIC
// Tool Versions:
// Description:   Protocol-agnostic memory request/response interface.
//                Abstracts memory protocol details from core logic,
//                enabling easy switching between AXI4, CHI, TileLink, etc.
//
// Dependencies:  riscv_core_pkg.sv
//
// Revision:
// Revision 1.0.0 - File Created
// Additional Comments:
//
////////////////////////////////////////////////////////////////////////////////

`timescale 1ns/1ps
`default_nettype none

// Memory request/response types
typedef struct packed {
    addr_t       addr;      // Memory address
    logic [2:0]  size;      // Transfer size (1, 2, 4, 8 bytes)
    logic        write;     // 1=write, 0=read
    word_t       data;      // Write data
    logic [3:0]  strb;      // Write strobes
    logic [3:0]  id;        // Transaction ID
    logic        cacheable; // Cacheable transaction
    logic [1:0]  prot;      // Protection level
} memory_req_t;

typedef struct packed {
    word_t       data;      // Read data
    logic [3:0]  id;        // Transaction ID
    logic        error;     // Error flag
    logic        last;      // Last beat of burst
} memory_rsp_t;

// Protocol-agnostic memory request/response interface
interface memory_req_rsp_if;
    import riscv_core_pkg::*;
    
    // Request channel
    logic        req_valid;
    logic        req_ready;
    memory_req_t req;
    
    // Response channel
    logic        rsp_valid;
    logic        rsp_ready;
    memory_rsp_t rsp;
    
    // Clock and reset (for protocol adapters)
    logic        clk;
    logic        rst_n;
    
    // Modport for master (cache, memory controller)
    modport master (
        output req_valid, req,
        input  req_ready, rsp_valid, rsp,
        output rsp_ready,
        input  clk, rst_n
    );
    
    // Modport for slave (protocol adapter)
    modport slave (
        input  req_valid, req,
        output req_ready, rsp_valid, rsp,
        input  rsp_ready,
        input  clk, rst_n
    );
    
    // Modport for monitor (testbench)
    modport monitor (
        input  req_valid, req, req_ready,
        input  rsp_valid, rsp, rsp_ready,
        input  clk, rst_n
    );
    
    // Clocking block for synchronous operations
    clocking cb @(posedge clk);
        input  req_valid, req, req_ready;
        input  rsp_valid, rsp, rsp_ready;
        input  rst_n;
    endclocking
    
    // Default clocking for testbench
    default clocking cb;
    
    // Task to send a memory request
    task automatic send_request(
        input  memory_req_t request,
        output logic success
    );
        success = 0;
        req = request;
        req_valid = 1;
        
        @(cb);
        while (!req_ready) @(cb);
        
        req_valid = 0;
        success = 1;
    endtask
    
    // Task to receive a memory response
    task automatic receive_response(
        output memory_rsp_t response,
        output logic success
    );
        success = 0;
        rsp_ready = 1;
        
        @(cb);
        while (!rsp_valid) @(cb);
        
        response = rsp;
        rsp_ready = 0;
        success = 1;
    endtask
    
    // Task to perform a complete read transaction
    task automatic read_transaction(
        input  addr_t addr,
        input  logic [2:0] size,
        input  logic [3:0] id,
        output word_t data,
        output logic error,
        output logic success
    );
        memory_req_t req;
        memory_rsp_t rsp;
        
        // Prepare request
        req.addr = addr;
        req.size = size;
        req.write = 0;
        req.id = id;
        req.cacheable = 1;
        req.prot = 2'b10; // Privileged, secure
        
        // Send request
        send_request(req, success);
        if (!success) return;
        
        // Receive response
        receive_response(rsp, success);
        if (!success) return;
        
        // Check ID match
        if (rsp.id != id) begin
            success = 0;
            return;
        end
        
        data = rsp.data;
        error = rsp.error;
    endtask
    
    // Task to perform a complete write transaction
    task automatic write_transaction(
        input  addr_t addr,
        input  logic [2:0] size,
        input  word_t data,
        input  logic [3:0] strb,
        input  logic [3:0] id,
        output logic error,
        output logic success
    );
        memory_req_t req;
        memory_rsp_t rsp;
        
        // Prepare request
        req.addr = addr;
        req.size = size;
        req.write = 1;
        req.data = data;
        req.strb = strb;
        req.id = id;
        req.cacheable = 1;
        req.prot = 2'b10; // Privileged, secure
        
        // Send request
        send_request(req, success);
        if (!success) return;
        
        // Receive response
        receive_response(rsp, success);
        if (!success) return;
        
        // Check ID match
        if (rsp.id != id) begin
            success = 0;
            return;
        end
        
        error = rsp.error;
    endtask
    
    // Function to check if interface is idle
    function automatic logic is_idle();
        return !req_valid && !rsp_valid;
    endfunction
    
    // Function to reset interface
    function automatic void reset_if();
        req_valid = 0;
        rsp_ready = 0;
        req = '0;
        rsp = '0;
    endfunction

endinterface : memory_req_rsp_if

`default_nettype wire 