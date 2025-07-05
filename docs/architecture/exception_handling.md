# Exception Handling Architecture

## Overview

The RISC-V core implements a comprehensive exception handling system that manages various types of exceptions and interrupts according to the RISC-V specification. This document describes the exception types, handling mechanisms, and implementation details.

**Status:** ✅ **IMPLEMENTED** - Phase 1 Complete  
**Last Updated:** 2025-07-05  

## Architecture Overview

The exception handling system consists of several key components:

1. **Exception Handler Module** (`exception_handler.sv`) - Central exception coordination
2. **Pipeline Stage Exception Detection** - Distributed exception detection across stages
3. **Enhanced CSR File** - Complete M-mode CSR support
4. **Pipeline Integration** - Exception propagation and PC redirection

### System Block Diagram
```
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   Fetch Stage   │    │  Execute Stage  │    │  Memory Stage   │
│                 │    │                 │    │                 │
│ • Instr Misalign│    │ • Illegal Instr │    │ • Load/Store    │
│ • Instr Fault   │    │ • Div by Zero   │    │   Misalignment  │
│ • Access Fault  │    │ • Overflow      │    │ • Access Faults │
│                 │    │ • ECALL/EBREAK  │    │                 │
└─────────┬───────┘    └─────────┬───────┘    └─────────┬───────┘
          │                      │                      │
          └──────────────────────┼──────────────────────┘
                                 │
                    ┌────────────▼──────────────┐
                    │   Exception Handler       │
                    │                           │
                    │ • Priority Resolution     │
                    │ • Interrupt Masking       │
                    │ • Vector Generation       │
                    │ • Exception Selection     │
                    └─────────────┬─────────────┘
                                  │
                    ┌─────────────▼─────────────┐
                    │   CSR File                │
                    │                           │
                    │ • MEPC, MCAUSE, MTVAL     │
                    │ • MIE, MIP, MTVEC         │
                    │ • Context Save/Restore    │
                    └─────────────┬─────────────┘
                                  │
                    ┌─────────────▼─────────────┐
                    │   Pipeline Control        │
                    │                           │
                    │ • PC Redirect             │
                    │ • Pipeline Flush          │
                    │ • Exception Vector        │
                    └───────────────────────────┘
```

## Exception Types

### Synchronous Exceptions
Synchronous exceptions occur as a result of instruction execution and are handled immediately when detected.

#### Arithmetic Exceptions
```systemverilog
// Division by zero exception (Execute Stage)
assign div_by_zero = id_ex_reg_i.ctrl.div_en && fwd_operand_b == '0;

// Overflow exception (Execute Stage)
assign overflow_exception = ((id_ex_reg_i.ctrl.alu_op == ALU_OP_ADD || 
                             id_ex_reg_i.ctrl.alu_op == ALU_OP_SUB) && 
                            alu_overflow_flag);
```

#### Memory Exceptions
```systemverilog
// Load address misalignment (Memory Stage)
always_comb begin
    load_addr_misaligned = 1'b0;
    if (ex_mem_reg_i.ctrl.mem_read_en) begin
        case (ex_mem_reg_i.ctrl.funct3)
            3'b001: load_addr_misaligned = ex_mem_reg_i.alu_result[0]; // LH/LHU
            3'b010: load_addr_misaligned = |ex_mem_reg_i.alu_result[1:0]; // LW
        endcase
    end
end

// Store address misalignment (Memory Stage)
always_comb begin
    store_addr_misaligned = 1'b0;
    if (ex_mem_reg_i.ctrl.mem_write_en) begin
        case (ex_mem_reg_i.ctrl.funct3)
            3'b001: store_addr_misaligned = ex_mem_reg_i.alu_result[0]; // SH
            3'b010: store_addr_misaligned = |ex_mem_reg_i.alu_result[1:0]; // SW
        endcase
    end
end

// Memory access faults (Memory Stage)
assign load_access_fault = ex_mem_reg_i.ctrl.mem_read_en && 
                          data_rsp_valid_i && data_rsp_error_i;
assign store_access_fault = ex_mem_reg_i.ctrl.mem_write_en && 
                           data_rsp_valid_i && data_rsp_error_i;
```

#### Control Exceptions
```systemverilog
// Illegal instruction exception (Execute Stage)
always_comb begin
    illegal_instruction = 1'b0;
    case (id_ex_reg_i.ctrl.alu_op)
        ALU_OP_ADD, ALU_OP_SUB, ALU_OP_XOR, ALU_OP_OR, ALU_OP_AND,
        ALU_OP_SLL, ALU_OP_SRL, ALU_OP_SRA, ALU_OP_SLT, ALU_OP_SLTU,
        ALU_OP_LUI, ALU_OP_COPY_A, ALU_OP_COPY_B: illegal_instruction = 1'b0;
        default: illegal_instruction = 1'b1;
    endcase
end

// System call exceptions (Execute Stage)
assign ecall_exception = id_ex_reg_i.ctrl.csr_cmd_en && 
                        id_ex_reg_i.immediate[11:0] == 12'h000;
assign breakpoint_exception = id_ex_reg_i.ctrl.csr_cmd_en && 
                             id_ex_reg_i.immediate[11:0] == 12'h001;
```

#### Instruction Exceptions
```systemverilog
// Instruction address misalignment (Fetch Stage)
assign instr_addr_misaligned = pc_q[0]; // PC must be 2-byte aligned

// Instruction access fault (Fetch Stage)
assign instr_access_fault = instr_rsp_valid_i && instr_rsp_error_i;
```

### Asynchronous Exceptions (Interrupts)
Asynchronous exceptions occur independently of instruction execution and can be masked.

#### Machine Mode Interrupts
```systemverilog
// Interrupt detection with masking (Exception Handler)
assign interrupt_enabled = mstatus_mie_i;
assign interrupt_info_o.m_software_interrupt = mip_msip_i && mie_msie_i && interrupt_enabled;
assign interrupt_info_o.m_timer_interrupt = mip_mtip_i && mie_mtie_i && interrupt_enabled;
assign interrupt_info_o.m_external_interrupt = mip_meip_i && mie_meie_i && interrupt_enabled;
```

## Exception Handler Module

### Module Interface
```systemverilog
module exception_handler (
    input  logic        clk_i,
    input  logic        rst_ni,
    
    // Exception inputs from pipeline stages
    input  exception_info_t fetch_exception_i,
    input  exception_info_t execute_exception_i,
    input  exception_info_t memory_exception_i,
    input  exception_info_t writeback_exception_i,
    
    // Interrupt inputs
    input  logic        m_software_interrupt_i,
    input  logic        m_timer_interrupt_i,
    input  logic        m_external_interrupt_i,
    
    // CSR state inputs
    input  logic        mstatus_mie_i,
    input  logic        mie_msie_i, mie_mtie_i, mie_meie_i,
    input  logic        mip_msip_i, mip_mtip_i, mip_meip_i,
    input  addr_t       mtvec_base_i,
    input  logic [1:0]  mtvec_mode_i,
    
    // Exception outputs
    output logic        exception_valid_o,
    output exception_info_t exception_info_o,
    output addr_t       trap_vector_o,
    output logic        pipeline_flush_o,
    output interrupt_info_t interrupt_info_o
);
```

### Priority Resolution
```systemverilog
// Exception priority encoding
typedef enum logic [3:0] {
    PRIO_NONE = 4'd0,
    PRIO_INTERRUPT = 4'd1,      // Highest priority
    PRIO_LOAD_FAULT = 4'd2,
    PRIO_STORE_FAULT = 4'd3,
    PRIO_INSTR_FAULT = 4'd4,
    PRIO_BREAKPOINT = 4'd5,
    PRIO_ECALL = 4'd6,
    PRIO_MISALIGNED = 4'd7,
    PRIO_ILLEGAL = 4'd8,
    PRIO_DIV_ZERO = 4'd9,
    PRIO_OVERFLOW = 4'd10       // Lowest priority
} exception_priority_e;

// Priority resolution logic
always_comb begin
    selected_exception = '0; // Default to no exception
    
    // Check interrupts first (highest priority)
    if (interrupt_detected.valid) begin
        selected_exception = interrupt_detected;
    end
    // Check pipeline exceptions in priority order
    else if (fetch_exception_detected.valid && 
             fetch_exception_detected.priority == highest_priority) begin
        selected_exception = fetch_exception_detected;
    end
    // ... similar for other stages
end
```

### Trap Vector Generation
```systemverilog
// Trap vector calculation
always_comb begin
    if (selected_exception.valid) begin
        if (selected_exception.exc_type == EXC_TYPE_INTERRUPT) begin
            // Interrupts always use vectored mode if enabled
            if (mtvec_mode_i == 2'b01) begin
                trap_vector_o = {mtvec_base_i[31:2], 2'b00} + 
                               (selected_exception.cause << 2);
            end else begin
                trap_vector_o = {mtvec_base_i[31:2], 2'b00};
            end
        end else begin
            // Exceptions use vectored mode if enabled
            if (mtvec_mode_i == 2'b01) begin
                trap_vector_o = {mtvec_base_i[31:2], 2'b00} + 
                               (selected_exception.cause << 2);
            end else begin
                trap_vector_o = {mtvec_base_i[31:2], 2'b00};
            end
        end
    end else begin
        trap_vector_o = '0;
    end
end
```

## Enhanced CSR Implementation

### CSR File Interface
```systemverilog
module csr_regfile (
    input  logic        clk_i,
    input  logic        rst_ni,
    
    // CSR access interface
    input  logic [11:0] csr_addr_i,
    input  logic [2:0]  csr_op_i,
    input  logic        write_en_i,
    input  word_t       rs1_data_i,
    output word_t       read_data_o,
    
    // Trap control interface
    input  logic        trap_en_i,
    input  logic        mret_en_i,
    input  addr_t       mepc_i,
    input  word_t       mcause_i,
    input  word_t       mtval_i,
    
    // Enhanced outputs
    output addr_t       mepc_o,
    output addr_t       mtvec_o,
    output word_t       mstatus_o,
    output word_t       mie_o,
    output word_t       mip_o,
    output word_t       mcause_o,
    output word_t       mtval_o,
    output logic        mstatus_mie_o,
    output logic [1:0]  mtvec_mode_o,
    output addr_t       mtvec_base_o
);
```

### Key CSR Registers

#### MSTATUS (Machine Status Register)
```systemverilog
// MSTATUS bit fields
typedef struct packed {
    logic [31:8] reserved;     // Reserved bits
    logic        mpie;         // Previous interrupt enable
    logic [6:4]  reserved2;    // Reserved bits
    logic        mie;          // Machine interrupt enable
    logic [2:0]  reserved3;    // Reserved bits
} mstatus_t;

// MSTATUS handling during traps
always_ff @(posedge clk_i) begin
    if (trap_en_i) begin
        // Save current MIE to MPIE, clear MIE
        mstatus_q <= {mstatus_q[31:8], mstatus_q[3], mstatus_q[6:4], 1'b0, mstatus_q[2:0]};
    end else if (mret_en_i) begin
        // Restore MPIE to MIE
        mstatus_q <= {mstatus_q[31:8], 1'b1, mstatus_q[6:4], mstatus_q[7], mstatus_q[2:0]};
    end
end
```

#### MTVEC (Machine Trap Vector Base Address)
```systemverilog
// MTVEC structure
typedef struct packed {
    logic [29:0] base;         // Base address (aligned to 4 bytes)
    logic [1:0]  mode;         // Vector mode
} mtvec_t;

// Vector modes
localparam logic [1:0] MTVEC_MODE_DIRECT = 2'b00;   // All traps to base
localparam logic [1:0] MTVEC_MODE_VECTORED = 2'b01; // Different handlers
```

#### MCAUSE (Machine Cause Register)
```systemverilog
// MCAUSE structure
typedef struct packed {
    logic        interrupt;    // 1=interrupt, 0=exception
    logic [30:0] cause;        // Exception/interrupt cause
} mcause_t;

// Exception cause codes
parameter logic [31:0] EXC_CAUSE_INSTR_ADDR_MISALIGNED = 32'h00000000;
parameter logic [31:0] EXC_CAUSE_INSTR_ACCESS_FAULT   = 32'h00000001;
parameter logic [31:0] EXC_CAUSE_ILLEGAL_INSTRUCTION  = 32'h00000002;
parameter logic [31:0] EXC_CAUSE_BREAKPOINT          = 32'h00000003;
parameter logic [31:0] EXC_CAUSE_LOAD_ADDR_MISALIGNED = 32'h00000004;
parameter logic [31:0] EXC_CAUSE_LOAD_ACCESS_FAULT   = 32'h00000005;
parameter logic [31:0] EXC_CAUSE_STORE_ADDR_MISALIGNED = 32'h00000006;
parameter logic [31:0] EXC_CAUSE_STORE_ACCESS_FAULT  = 32'h00000007;
parameter logic [31:0] EXC_CAUSE_ECALL_M            = 32'h0000000B;

// Interrupt cause codes
parameter logic [31:0] EXC_CAUSE_M_SOFTWARE_INTERRUPT = 32'h80000003;
parameter logic [31:0] EXC_CAUSE_M_TIMER_INTERRUPT    = 32'h80000007;
parameter logic [31:0] EXC_CAUSE_M_EXTERNAL_INTERRUPT = 32'h8000000B;
```

## Pipeline Integration

### Exception Propagation Through Pipeline
```systemverilog
// Exception information structure
typedef struct packed {
    logic              valid;           // Exception is valid
    exception_type_e   exc_type;        // Exception type (interrupt/exception)
    exception_cause_t  cause;           // Exception cause code
    addr_t             pc;              // PC where exception occurred
    word_t             tval;            // Exception-specific value
    exception_priority_e priority;      // Exception priority
} exception_info_t;

// Pipeline register updates
always_ff @(posedge clk_i) begin
    if (!stall_m_i) begin
        if (flush_e_i) begin
            ex_mem_reg_q.exception.valid <= 1'b0; // Clear exception on flush
        end else begin
            ex_mem_reg_q.exception <= exception_detected; // Latch exception info
        end
    end
end
```

### PC Redirection and Pipeline Flush
```systemverilog
// Exception PC redirect logic (in riscv_core.sv)
assign pc_redirect_exception = exception_valid;
assign pc_redirect_target_exception = trap_vector;

// Combine normal PC redirect with exception redirect
assign pc_redirect_combined = pc_redirect || pc_redirect_exception;
assign pc_redirect_target_combined = pc_redirect_exception ? 
                                   pc_redirect_target_exception : 
                                   pc_redirect_target;
```

## Interrupt Handling

### Interrupt Detection and Masking
```systemverilog
// Interrupt detection with proper masking
always_comb begin
    interrupt_enabled = mstatus_mie_i;
    
    // Detect enabled and pending interrupts
    interrupt_info_o.m_software_interrupt = mip_msip_i && mie_msie_i && interrupt_enabled;
    interrupt_info_o.m_timer_interrupt = mip_mtip_i && mie_mtie_i && interrupt_enabled;
    interrupt_info_o.m_external_interrupt = mip_meip_i && mie_meie_i && interrupt_enabled;
    
    // Determine if any interrupt is pending
    interrupt_info_o.interrupt_pending = interrupt_info_o.m_software_interrupt ||
                                        interrupt_info_o.m_timer_interrupt ||
                                        interrupt_info_o.m_external_interrupt;
end
```

### Interrupt Priority Resolution
```systemverilog
// Interrupt priority (external > timer > software)
always_comb begin
    interrupt_info_o.interrupt_cause = EXC_CAUSE_M_SOFTWARE_INTERRUPT; // Default
    if (interrupt_info_o.m_external_interrupt) begin
        interrupt_info_o.interrupt_cause = EXC_CAUSE_M_EXTERNAL_INTERRUPT;
    end else if (interrupt_info_o.m_timer_interrupt) begin
        interrupt_info_o.interrupt_cause = EXC_CAUSE_M_TIMER_INTERRUPT;
    end else if (interrupt_info_o.m_software_interrupt) begin
        interrupt_info_o.interrupt_cause = EXC_CAUSE_M_SOFTWARE_INTERRUPT;
    end
end
```

## Exception Recovery

### Return from Exception (MRET)
```systemverilog
// MRET instruction handling
always_ff @(posedge clk_i) begin
    if (mret_en_i) begin
        // Restore previous interrupt-enable state
        mstatus_q <= {mstatus_q[31:8], 1'b1, mstatus_q[6:4], mstatus_q[7], mstatus_q[2:0]};
    end
end

// PC redirection for MRET
assign pc_redirect_mret = mret_en_i;
assign pc_target_mret = mepc_q; // Return to saved PC
```

### Context Saving and Restoration
```systemverilog
// Context saving on trap
always_ff @(posedge clk_i) begin
    if (trap_en_i) begin
        // Save exception PC
        mepc_q <= mepc_i;
        
        // Save exception cause
        mcause_q <= mcause_i;
        
        // Save exception value
        mtval_q <= mtval_i;
    end
end
```

## Performance Considerations

### Exception Latency
- **Detection Latency:** 1-3 cycles (depending on pipeline stage)
- **Handler Entry:** 1 cycle (PC redirect)
- **Context Save:** 1 cycle (CSR updates)
- **Total Latency:** 3-5 cycles from exception to handler

### Interrupt Response Time
- **Interrupt Detection:** 1 cycle
- **Priority Resolution:** 1 cycle
- **Handler Entry:** 1 cycle
- **Total Response:** 3 cycles

### Pipeline Efficiency
- **Exception Flush:** Clears pipeline to prevent side effects
- **MRET Recovery:** Restores pipeline state efficiently
- **Interrupt Masking:** Prevents interrupt storms

## Testing and Verification

### Exception Test Scenarios
1. **Illegal Instruction:** Execute unimplemented opcode
2. **Division by Zero:** Divide by zero operand
3. **Memory Misalignment:** Access unaligned addresses
4. **System Calls:** Execute ECALL/EBREAK instructions
5. **Interrupts:** Generate software/timer/external interrupts
6. **Priority Testing:** Multiple simultaneous exceptions
7. **Vector Mode:** Test both direct and vectored trap modes

### Verification Checklist
- [ ] All exception types detected correctly
- [ ] Exception priorities respected
- [ ] Context saved and restored properly
- [ ] Interrupt masking works correctly
- [ ] Trap vectors generated correctly
- [ ] Pipeline flush on exceptions
- [ ] MRET instruction works properly
- [ ] Performance meets requirements

## Future Enhancements

### Planned Improvements
1. **Exception Delegation:** Support for S-mode exception delegation
2. **Performance Counters:** Exception/interrupt performance monitoring
3. **Debug Support:** Enhanced breakpoint and watchpoint support
4. **Vector Exceptions:** Support for vector instruction exceptions
5. **Floating-Point Exceptions:** FPU exception handling (basic implemented)

### Extensibility
The exception handling system is designed to be easily extensible:
- New exception types can be added to the priority system
- Additional CSR registers can be integrated
- Different privilege modes can be supported
- Custom exception handlers can be implemented 