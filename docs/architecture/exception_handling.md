# Exception Handling Architecture

## Overview

The RISC-V core implements a comprehensive exception handling system that manages various types of exceptions and interrupts according to the RISC-V specification. This document describes the exception types, handling mechanisms, and implementation details.

## Exception Types

### Synchronous Exceptions
Synchronous exceptions occur as a result of instruction execution and are handled immediately when detected.

#### Arithmetic Exceptions
```systemverilog
// Division by zero exception
assign div_by_zero_exception = (div_en && (rs2_data == 32'h0));

// Overflow exception (for ADD/SUB with overflow detection)
assign overflow_exception = alu_overflow && overflow_enable;
```

#### Memory Exceptions
```systemverilog
// Misaligned memory access
assign load_addr_misaligned = (mem_read_en && 
    ((mem_access_type == MEM_WORD && mem_addr[1:0] != 2'b00) ||
     (mem_access_type == MEM_HALF && mem_addr[0] != 1'b0)));

assign store_addr_misaligned = (mem_write_en && 
    ((mem_access_type == MEM_WORD && mem_addr[1:0] != 2'b00) ||
     (mem_access_type == MEM_HALF && mem_addr[0] != 1'b0)));

// Memory access fault (page fault, protection violation)
assign load_access_fault = mem_read_en && mem_access_fault;
assign store_access_fault = mem_write_en && mem_access_fault;
```

#### Control Exceptions
```systemverilog
// Illegal instruction exception
assign illegal_instruction = !valid_instruction && instruction_valid;

// Breakpoint exception
assign breakpoint_exception = (instr == EBREAK_INSTRUCTION);

// Environment call exception
assign ecall_exception = (instr == ECALL_INSTRUCTION);
```

### Asynchronous Exceptions (Interrupts)
Asynchronous exceptions occur independently of instruction execution and can be masked.

#### Machine Mode Interrupts
```systemverilog
// Software interrupt (MSIP)
assign m_software_interrupt = mip.msip && mie.msie && mstatus.mie;

// Timer interrupt (MTIP)
assign m_timer_interrupt = mip.mtip && mie.mtie && mstatus.mie;

// External interrupt (MEIP)
assign m_external_interrupt = mip.meip && mie.meie && mstatus.mie;
```

## Exception Handling Flow

### Exception Detection
```systemverilog
// Exception detection in execute stage
always @(posedge clk_i) begin
    if (rst_ni) begin
        // Detect exceptions based on instruction type
        case (instruction_type)
            INSTR_ALU: begin
                exception_valid <= overflow_exception;
                exception_cause <= EXC_CAUSE_OVERFLOW;
            end
            INSTR_MEM: begin
                exception_valid <= load_addr_misaligned || load_access_fault;
                exception_cause <= load_addr_misaligned ? EXC_CAUSE_LOAD_ADDR_MISALIGNED : 
                                                   EXC_CAUSE_LOAD_ACCESS_FAULT;
            end
            INSTR_DIV: begin
                exception_valid <= div_by_zero_exception;
                exception_cause <= EXC_CAUSE_DIVIDE_BY_ZERO;
            end
            INSTR_SYSTEM: begin
                exception_valid <= ecall_exception || breakpoint_exception;
                exception_cause <= ecall_exception ? EXC_CAUSE_ECALL_M : EXC_CAUSE_BREAKPOINT;
            end
            default: begin
                exception_valid <= illegal_instruction;
                exception_cause <= EXC_CAUSE_ILLEGAL_INSTRUCTION;
            end
        endcase
    end
end
```

### Exception Priority
```systemverilog
// Exception priority encoding
typedef enum logic [3:0] {
    PRIO_NONE = 4'd0,
    PRIO_INTERRUPT = 4'd1,
    PRIO_LOAD_FAULT = 4'd2,
    PRIO_STORE_FAULT = 4'd3,
    PRIO_INSTR_FAULT = 4'd4,
    PRIO_BREAKPOINT = 4'd5,
    PRIO_ECALL = 4'd6,
    PRIO_MISALIGNED = 4'd7,
    PRIO_ILLEGAL = 4'd8,
    PRIO_DIV_ZERO = 4'd9,
    PRIO_OVERFLOW = 4'd10
} exception_priority_e;

// Priority resolution
always @(*) begin
    case (1'b1)
        m_external_interrupt:  exception_priority = PRIO_INTERRUPT;
        m_timer_interrupt:     exception_priority = PRIO_INTERRUPT;
        m_software_interrupt:  exception_priority = PRIO_INTERRUPT;
        load_access_fault:     exception_priority = PRIO_LOAD_FAULT;
        store_access_fault:    exception_priority = PRIO_STORE_FAULT;
        instr_access_fault:    exception_priority = PRIO_INSTR_FAULT;
        breakpoint_exception:  exception_priority = PRIO_BREAKPOINT;
        ecall_exception:       exception_priority = PRIO_ECALL;
        load_addr_misaligned:  exception_priority = PRIO_MISALIGNED;
        store_addr_misaligned: exception_priority = PRIO_MISALIGNED;
        illegal_instruction:   exception_priority = PRIO_ILLEGAL;
        div_by_zero_exception: exception_priority = PRIO_DIV_ZERO;
        overflow_exception:    exception_priority = PRIO_OVERFLOW;
        default:               exception_priority = PRIO_NONE;
    endcase
end
```

### Exception Vector Generation
```systemverilog
// Exception vector calculation
always @(*) begin
    case (exception_type)
        EXC_TYPE_INTERRUPT: begin
            exception_vector = mtvec_base + (exception_cause << 2);
        end
        EXC_TYPE_EXCEPTION: begin
            if (mtvec_mode == MTVEC_MODE_VECTORED) begin
                exception_vector = mtvec_base + (exception_cause << 2);
            end else begin
                exception_vector = mtvec_base;
            end
        end
        default: begin
            exception_vector = mtvec_base;
        end
    endcase
end
```

## CSR (Control and Status Registers)

### Machine Mode CSRs
```systemverilog
// Machine Information Registers
typedef struct packed {
    logic [31:0] vendorid;    // Vendor ID
    logic [31:0] archid;      // Architecture ID
    logic [31:0] impid;       // Implementation ID
    logic [31:0] hartid;      // Hardware thread ID
} machine_info_csrs_t;

// Machine Trap Setup
typedef struct packed {
    logic [31:0] mstatus;     // Machine status register
    logic [31:0] misa;        // ISA and extensions
    logic [31:0] medeleg;     // Machine exception delegation
    logic [31:0] mideleg;     // Machine interrupt delegation
    logic [31:0] mie;         // Machine interrupt enable
    logic [31:0] mtvec;       // Machine trap vector base address
    logic [31:0] mcounteren;  // Machine counter enable
} machine_trap_setup_csrs_t;

// Machine Trap Handling
typedef struct packed {
    logic [31:0] mscratch;    // Machine scratch register
    logic [31:0] mepc;        // Machine exception program counter
    logic [31:0] mcause;      // Machine trap cause
    logic [31:0] mtval;       // Machine trap value
    logic [31:0] mip;         // Machine interrupt pending
} machine_trap_handling_csrs_t;
```

### CSR Implementation
```systemverilog
module csr_regfile (
    input  logic        clk_i,
    input  logic        rst_ni,
    
    // CSR access interface
    input  logic        csr_read_en_i,
    input  logic        csr_write_en_i,
    input  csr_addr_t   csr_addr_i,
    input  word_t       csr_write_data_i,
    output word_t       csr_read_data_o,
    
    // Exception interface
    input  logic        exception_valid_i,
    input  exception_cause_t exception_cause_i,
    input  addr_t       exception_pc_i,
    input  word_t       exception_tval_i,
    output addr_t       exception_vector_o,
    
    // Interrupt interface
    input  logic        m_software_interrupt_i,
    input  logic        m_timer_interrupt_i,
    input  logic        m_external_interrupt_i,
    
    // CSR outputs
    output machine_info_csrs_t        machine_info_o,
    output machine_trap_setup_csrs_t  machine_trap_setup_o,
    output machine_trap_handling_csrs_t machine_trap_handling_o
);

    // CSR memory
    machine_info_csrs_t        machine_info;
    machine_trap_setup_csrs_t  machine_trap_setup;
    machine_trap_handling_csrs_t machine_trap_handling;
    
    // CSR read logic
    always @(*) begin
        case (csr_addr_i)
            // Machine Information
            CSR_MVENDORID:  csr_read_data_o = machine_info.vendorid;
            CSR_MARCHID:    csr_read_data_o = machine_info.archid;
            CSR_MIMPID:     csr_read_data_o = machine_info.impid;
            CSR_MHARTID:    csr_read_data_o = machine_info.hartid;
            
            // Machine Trap Setup
            CSR_MSTATUS:    csr_read_data_o = machine_trap_setup.mstatus;
            CSR_MISA:       csr_read_data_o = machine_trap_setup.misa;
            CSR_MEDELEG:    csr_read_data_o = machine_trap_setup.medeleg;
            CSR_MIDELEG:    csr_read_data_o = machine_trap_setup.mideleg;
            CSR_MIE:        csr_read_data_o = machine_trap_setup.mie;
            CSR_MTVEC:      csr_read_data_o = machine_trap_setup.mtvec;
            CSR_MCOUNTEREN: csr_read_data_o = machine_trap_setup.mcounteren;
            
            // Machine Trap Handling
            CSR_MSCRATCH:   csr_read_data_o = machine_trap_handling.mscratch;
            CSR_MEPC:       csr_read_data_o = machine_trap_handling.mepc;
            CSR_MCAUSE:     csr_read_data_o = machine_trap_handling.mcause;
            CSR_MTVAL:      csr_read_data_o = machine_trap_handling.mtval;
            CSR_MIP:        csr_read_data_o = machine_trap_handling.mip;
            
            default:        csr_read_data_o = 32'h0;
        endcase
    end
    
    // CSR write logic
    always @(posedge clk_i) begin
        if (rst_ni && csr_write_en_i) begin
            case (csr_addr_i)
                CSR_MSTATUS:    machine_trap_setup.mstatus <= csr_write_data_i;
                CSR_MISA:       machine_trap_setup.misa <= csr_write_data_i;
                CSR_MEDELEG:    machine_trap_setup.medeleg <= csr_write_data_i;
                CSR_MIDELEG:    machine_trap_setup.mideleg <= csr_write_data_i;
                CSR_MIE:        machine_trap_setup.mie <= csr_write_data_i;
                CSR_MTVEC:      machine_trap_setup.mtvec <= csr_write_data_i;
                CSR_MCOUNTEREN: machine_trap_setup.mcounteren <= csr_write_data_i;
                CSR_MSCRATCH:   machine_trap_handling.mscratch <= csr_write_data_i;
                CSR_MEPC:       machine_trap_handling.mepc <= csr_write_data_i;
                CSR_MCAUSE:     machine_trap_handling.mcause <= csr_write_data_i;
                CSR_MTVAL:      machine_trap_handling.mtval <= csr_write_data_i;
                CSR_MIP:        machine_trap_handling.mip <= csr_write_data_i;
            endcase
        end
    end
    
    // Exception handling
    always @(posedge clk_i) begin
        if (rst_ni && exception_valid_i) begin
            // Save exception PC
            machine_trap_handling.mepc <= exception_pc_i;
            
            // Save exception cause
            machine_trap_handling.mcause <= {1'b0, exception_cause_i};
            
            // Save exception value
            machine_trap_handling.mtval <= exception_tval_i;
            
            // Update MIP for interrupts
            if (m_software_interrupt_i) machine_trap_handling.mip.msip <= 1'b1;
            if (m_timer_interrupt_i) machine_trap_handling.mip.mtip <= 1'b1;
            if (m_external_interrupt_i) machine_trap_handling.mip.meip <= 1'b1;
        end
    end
    
    // Exception vector generation
    always @(*) begin
        if (exception_valid_i) begin
            if (machine_trap_setup.mtvec[1:0] == 2'b01) begin
                // Vectored mode
                exception_vector_o = {machine_trap_setup.mtvec[31:2], 2'b00} + 
                                   (exception_cause_i << 2);
            end else begin
                // Direct mode
                exception_vector_o = {machine_trap_setup.mtvec[31:2], 2'b00};
            end
        end else begin
            exception_vector_o = 32'h0;
        end
    end
    
    // Output assignments
    assign machine_info_o = machine_info;
    assign machine_trap_setup_o = machine_trap_setup;
    assign machine_trap_handling_o = machine_trap_handling;

endmodule
```

## Pipeline Integration

### Exception Propagation
```systemverilog
// Exception propagation through pipeline
always @(posedge clk_i) begin
    if (rst_ni) begin
        // Propagate exceptions through pipeline registers
        if (!stall_ex) begin
            ex_mem_reg_m_i.exception_valid <= exception_valid_ex;
            ex_mem_reg_m_i.exception_cause <= exception_cause_ex;
            ex_mem_reg_m_i.exception_pc <= pc_ex;
            ex_mem_reg_m_i.exception_tval <= exception_tval_ex;
        end
        
        if (!stall_m) begin
            mem_wb_reg_w_i.exception_valid <= ex_mem_reg_m_i.exception_valid;
            mem_wb_reg_w_i.exception_cause <= ex_mem_reg_m_i.exception_cause;
            mem_wb_reg_w_i.exception_pc <= ex_mem_reg_m_i.exception_pc;
            mem_wb_reg_w_i.exception_tval <= ex_mem_reg_m_i.exception_tval;
        end
    end
end
```

### Pipeline Flush
```systemverilog
// Pipeline flush on exception
always @(posedge clk_i) begin
    if (rst_ni) begin
        if (exception_valid_w) begin
            // Flush pipeline
            flush_f <= 1'b1;
            flush_d <= 1'b1;
            flush_ex <= 1'b1;
            flush_m <= 1'b1;
            
            // Redirect PC to exception vector
            pc_redirect <= 1'b1;
            pc_target <= exception_vector;
        end else begin
            flush_f <= 1'b0;
            flush_d <= 1'b0;
            flush_ex <= 1'b0;
            flush_m <= 1'b0;
            pc_redirect <= 1'b0;
        end
    end
end
```

## Interrupt Handling

### Interrupt Detection
```systemverilog
// Interrupt detection logic
always @(posedge clk_i) begin
    if (rst_ni) begin
        // Check for pending interrupts
        interrupt_pending <= m_software_interrupt || 
                           m_timer_interrupt || 
                           m_external_interrupt;
        
        // Interrupt priority
        if (m_external_interrupt) begin
            interrupt_cause <= EXC_CAUSE_M_EXTERNAL_INTERRUPT;
        end else if (m_timer_interrupt) begin
            interrupt_cause <= EXC_CAUSE_M_TIMER_INTERRUPT;
        end else if (m_software_interrupt) begin
            interrupt_cause <= EXC_CAUSE_M_SOFTWARE_INTERRUPT;
        end
    end
end
```

### Interrupt Service Routine
```systemverilog
// Interrupt service routine entry
always @(posedge clk_i) begin
    if (rst_ni && interrupt_pending && !exception_valid_ex) begin
        // Save current PC
        mepc_save <= pc_f_o;
        
        // Disable interrupts
        mstatus_mie_clear <= 1'b1;
        
        // Jump to interrupt handler
        pc_redirect <= 1'b1;
        pc_target <= interrupt_vector;
    end
end
```

## Exception Recovery

### Return from Exception
```systemverilog
// MRET instruction handling
always @(posedge clk_i) begin
    if (rst_ni && mret_execute) begin
        // Restore PC from MEPC
        pc_redirect <= 1'b1;
        pc_target <= mepc;
        
        // Re-enable interrupts
        mstatus_mie_restore <= 1'b1;
        
        // Flush pipeline
        flush_f <= 1'b1;
        flush_d <= 1'b1;
        flush_ex <= 1'b1;
        flush_m <= 1'b1;
    end
end
```

### Exception Context Saving
```systemverilog
// Context saving on exception
always @(posedge clk_i) begin
    if (rst_ni && exception_valid_w) begin
        // Save general-purpose registers
        for (int i = 0; i < 32; i++) begin
            context_regs[i] <= reg_file[i];
        end
        
        // Save floating-point registers (if implemented)
        // Save vector registers (if implemented)
        
        // Save additional state
        context_pc <= pc_w;
        context_cause <= exception_cause_w;
        context_tval <= exception_tval_w;
    end
end
```

## Performance Considerations

### Exception Latency
- **Detection Latency:** 1-3 cycles (depending on pipeline stage)
- **Handling Latency:** 2-5 cycles (vector calculation + context save)
- **Recovery Latency:** 1-3 cycles (context restore + pipeline refill)

### Optimization Techniques
- **Fast Exception Path:** Dedicated exception handling logic
- **Context Switching:** Efficient register save/restore
- **Interrupt Vectoring:** Direct jump to interrupt handlers
- **Exception Bypassing:** Early exception detection

## Future Enhancements

### Phase 1: Enhanced Exception Handling
- **Complete M-mode Support:** All machine-mode exceptions
- **Exception Delegation:** S-mode and U-mode support
- **Advanced Interrupts:** PLIC (Platform-Level Interrupt Controller)
- **Performance Counters:** Hardware performance monitoring

### Phase 2: Virtual Memory Support
- **Memory Management Unit:** TLB and page tables
- **Page Fault Handling:** Demand paging support
- **Memory Protection:** User/supervisor mode separation
- **Address Translation:** Virtual to physical address mapping

### Phase 3: Advanced Features
- **Debug Support:** Hardware breakpoints and watchpoints
- **Trace Interface:** Instruction and data tracing
- **Security Extensions:** Trusted execution environment
- **Real-time Support:** Deterministic interrupt handling

---

**Exception Handling Version:** 1.0  
**Last Updated:** June 2025  
**Core Version:** RV32IM 5-stage Pipeline 