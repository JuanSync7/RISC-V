# RISC-V Pipeline Architecture

## Overview

The RISC-V core implements a classic 5-stage pipeline architecture optimized for RV32IM instruction set support. This document provides a detailed description of the pipeline stages, their interactions, and performance characteristics.

## Pipeline Stages

### 1. Fetch Stage (F)
**Location:** `rtl/core/fetch_stage.sv`

**Responsibilities:**
- Program Counter (PC) management
- Instruction fetching via AXI4-Lite interface
- Branch prediction integration
- PC redirection handling

**Key Features:**
- **Branch Prediction Unit (BPU):** 2-bit saturating counter with BTB/BHT
- **AXI4-Lite Interface:** Memory-mapped instruction fetch
- **PC Selection Logic:** Priority-based next PC selection
- **Pipeline Register:** IF/ID register for stage decoupling

**Performance Characteristics:**
- **Latency:** 1 cycle (with memory wait states)
- **Throughput:** 1 instruction per cycle (ideal)
- **Branch Prediction:** >85% accuracy target

### 2. Decode Stage (D)
**Location:** `rtl/core/decode_stage.sv`

**Responsibilities:**
- Instruction decoding and field extraction
- Register file read operations
- Control signal generation
- Hazard detection preparation

**Key Features:**
- **RV32IM Decoding:** Full instruction set support
- **Register File Interface:** Dual-port read operations
- **Control Signal Generation:** Comprehensive control logic
- **Immediate Generation:** All RISC-V immediate formats

**Decoded Instructions:**
- **RV32I Base:** Arithmetic, logical, memory, control flow
- **RV32M Multiply:** MUL, MULH, MULHSU, MULHU
- **RV32M Divide:** DIV, DIVU, REM, REMU
- **CSR Operations:** Machine-mode CSR access

### 3. Execute Stage (E)
**Location:** `rtl/core/execute_stage.sv`

**Responsibilities:**
- ALU operations and arithmetic
- Multi-cycle multiplication and division
- Branch condition evaluation
- Data forwarding logic

**Key Features:**
- **ALU Operations:** All RV32I arithmetic and logical operations
- **Multi-cycle Units:** Multiplication and division support
- **Branch Evaluation:** Complete branch condition logic
- **Data Forwarding:** EX/MEM and MEM/WB forwarding paths
- **Branch Prediction Updates:** BPU feedback mechanism

**Functional Units:**
- **Main ALU:** Single-cycle arithmetic/logical operations
- **Multiplier Unit:** Multi-cycle RV32M multiplication
- **Divider Unit:** Multi-cycle RV32M division with exception handling

### 4. Memory Stage (M)
**Location:** `rtl/core/mem_stage.sv`

**Responsibilities:**
- Load/store operations
- AXI4-Lite data memory interface
- Memory access coordination
- Pipeline register management

**Key Features:**
- **Load/Store Operations:** Byte, halfword, word access
- **AXI4-Lite Interface:** Memory-mapped data access
- **Memory Alignment:** Proper address alignment handling
- **Write-back Preparation:** Result forwarding to next stage

**Memory Operations:**
- **Load Instructions:** LB, LH, LW, LBU, LHU
- **Store Instructions:** SB, SH, SW
- **Address Calculation:** Base + offset addressing
- **Data Alignment:** Proper byte/halfword alignment

### 5. Writeback Stage (W)
**Location:** `rtl/core/writeback_stage.sv`

**Responsibilities:**
- Register file write operations
- Result multiplexing and selection
- Forwarding path management
- Pipeline completion

**Key Features:**
- **Register File Write:** Single-cycle register updates
- **Result Multiplexing:** ALU, memory, PC+4, CSR results
- **Forwarding Logic:** MEM/WB → EX forwarding
- **Pipeline Completion:** Instruction retirement

## Pipeline Registers

### IF/ID Register
```systemverilog
typedef struct packed {
    addr_t pc;        // Program counter
    word_t instr;     // Fetched instruction
    logic  valid;     // Instruction validity
} if_id_reg_t;
```

### ID/EX Register
```systemverilog
typedef struct packed {
    addr_t         pc;        // Program counter
    word_t         rs1_data;  // Source register 1 data
    word_t         rs2_data;  // Source register 2 data
    word_t         immediate; // Decoded immediate
    reg_addr_t     rd_addr;   // Destination register address
    reg_addr_t     rs1_addr;  // Source register 1 address (for forwarding)
    reg_addr_t     rs2_addr;  // Source register 2 address (for forwarding)
    ctrl_signals_t ctrl;      // Control signals
} id_ex_reg_t;
```

### EX/MEM Register
```systemverilog
typedef struct packed {
    word_t         alu_result;   // ALU result
    word_t         store_data;   // Data to store
    reg_addr_t     rd_addr;      // Destination register address
    logic          alu_overflow; // ALU overflow flag
    ctrl_signals_t ctrl;         // Control signals
} ex_mem_reg_t;
```

### MEM/WB Register
```systemverilog
typedef struct packed {
    word_t       wb_data;     // Write-back data
    reg_addr_t   rd_addr;     // Destination register address
    logic        reg_write_en; // Register write enable
    wb_mux_sel_e wb_mux_sel;  // Write-back multiplexer selection
} mem_wb_reg_t;
```

## Hazard Handling

### Data Hazards
**Types:**
- **RAW (Read After Write):** Most common, handled by forwarding
- **WAW (Write After Write):** Handled by register file design
- **WAR (Write After Read):** Not possible in this pipeline

**Forwarding Paths:**
- **EX/MEM → EX:** Forward ALU results to next instruction
- **MEM/WB → EX:** Forward memory/ALU results to next instruction

### Control Hazards
**Types:**
- **Branch Misprediction:** Handled by PC redirection
- **Jump Instructions:** Handled by PC redirection
- **Exception/Interrupt:** Handled by PC redirection

**Recovery Mechanism:**
- **Pipeline Flush:** Clear pipeline registers
- **PC Redirection:** Update program counter
- **Branch Prediction Update:** Learn from mispredictions

### Structural Hazards
**Types:**
- **Multi-cycle Operations:** Multiplication and division
- **Memory Access Conflicts:** Load/store operations

**Handling:**
- **Pipeline Stalling:** Stop pipeline progression
- **Resource Arbitration:** Coordinate access to shared resources

## Performance Analysis

### Ideal Performance
- **IPC (Instructions Per Cycle):** 1.0 (theoretical maximum)
- **Pipeline Efficiency:** 100% (no hazards)
- **Throughput:** 1 instruction per cycle

### Realistic Performance
- **IPC:** ~0.8 (typical for 5-stage pipeline)
- **Pipeline Efficiency:** ~70-80%
- **Performance Factors:**
  - Data hazards (forwarding reduces impact)
  - Control hazards (branch prediction reduces impact)
  - Structural hazards (multi-cycle operations)

### Performance Bottlenecks
1. **Memory Access:** Memory wait states reduce throughput
2. **Branch Mispredictions:** Pipeline flush penalty
3. **Multi-cycle Operations:** Multiplication and division stalls
4. **Data Hazards:** Forwarding reduces but doesn't eliminate

## Branch Prediction

### Branch Prediction Unit (BPU)
**Location:** `rtl/prediction/branch_predictor.sv`

**Features:**
- **2-bit Saturating Counter:** Predicts taken/not-taken
- **Branch Target Buffer (BTB):** 64-entry direct-mapped cache
- **Branch History Table (BHT):** 256-entry table with global history
- **Global History Register:** 8-bit branch history

**Prediction Logic:**
- **BTB Hit + BHT Counter:** Use BHT counter for prediction
- **BTB Miss:** Predict not-taken (sequential execution)
- **Update Mechanism:** Update both BTB and BHT on resolution

**Performance:**
- **Target Accuracy:** >85% for typical workloads
- **Prediction Latency:** 1 cycle
- **Update Latency:** 1 cycle (pipelined)

## Memory Interface

### AXI4-Lite Interface
**Features:**
- **Instruction Memory:** Read-only interface
- **Data Memory:** Read/write interface
- **Protocol Compliance:** Full AXI4-Lite specification
- **Burst Support:** Single transfers (Lite specification)

**Interface Signals:**
- **Address Channel:** ARADDR, ARVALID, ARREADY
- **Data Channel:** RDATA, RVALID, RREADY
- **Write Channel:** AWADDR, WDATA, WVALID, WREADY
- **Response Channel:** BRESP, BVALID, BREADY

### Memory Access Patterns
- **Instruction Fetch:** Sequential access (PC + 4)
- **Data Access:** Random access (base + offset)
- **Alignment:** Proper byte/halfword/word alignment
- **Endianness:** Little-endian (RISC-V standard)

## Exception Handling

### Exception Types
- **Arithmetic Exceptions:** Division by zero, overflow
- **Memory Exceptions:** Misaligned access, page faults
- **Control Exceptions:** Illegal instruction, breakpoint
- **System Exceptions:** ECALL, EBREAK

### Exception Handling Flow
1. **Exception Detection:** In execute stage
2. **Exception Vector:** Jump to exception handler
3. **Context Saving:** Save PC and status
4. **Handler Execution:** Process exception
5. **Context Restoration:** Restore state and resume

## Future Enhancements

### Phase 1 Improvements
- **Instruction Cache:** 4KB 2-way set associative
- **Enhanced Exception Handling:** Complete M-mode support

### Phase 2 Improvements
- **Data Cache:** Write-back data cache
- **Advanced Branch Prediction:** Tournament predictor

### Phase 3 Improvements
- **Superscalar Execution:** Multiple instructions per cycle
- **Out-of-Order Processing:** Dynamic instruction scheduling

---

**Document Version:** 1.0  
**Last Updated:** June 2025  
**Pipeline Version:** RV32IM 5-stage 