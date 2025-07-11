# RISC-V Core Current Implementation
## RV32IM Pipeline Architecture

**Project:** RV32IM Core  
**Version:** 1.2.0  
**Status:** ✅ Complete & Functional  
**Last Updated:** 2025-06-28  
**Architecture:** 5-Stage Pipeline (Fetch, Decode, Execute, Memory, Writeback)

---

## 📋 Core Overview

This is a complete, synthesizable RISC-V RV32IM core implementation featuring a 5-stage pipeline with full hazard detection, forwarding logic, and support for all RV32I base instructions plus RV32M multiplication and division extensions.

### 🎯 Key Features
- **Complete RV32IM Support:** All base integer and multiplication/division instructions
- **5-Stage Pipeline:** Optimized for performance and area efficiency
- **Advanced Hazard Handling:** Data hazards, control hazards, and structural hazards
- **AXI4 Memory Interface:** Industry-standard memory interface
- **CSR Support:** Basic control and status register operations
- **Exception Handling:** Basic exception detection and handling
- **Overflow Detection:** ALU overflow detection for arithmetic operations

---

## 🏗️ Architecture Overview

### Pipeline Stages
```
┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐
│  Fetch  │───▶│ Decode  │───▶│Execute  │───▶│ Memory  │───▶│Writeback│
│  Stage  │    │  Stage  │    │ Stage   │    │  Stage  │    │  Stage  │
└─────────┘    └─────────┘    └─────────┘    └─────────┘    └─────────┘
     │              │              │              │              │
     ▼              ▼              ▼              ▼              ▼
  PC + 4        Register      ALU/Mult/Div    Memory        Register
  Branch        Read          Operations      Access         Write
  Prediction    Hazard        Forwarding      AXI4          Hazard
  (Future)      Detection     Logic           Interface     Resolution
```

### Data Flow
- **Instruction Fetch:** AXI4-Lite interface to instruction memory
- **Register Read:** 32x32 register file with dual read ports
- **Execute:** ALU, multiplier, divider, branch logic
- **Memory:** AXI4-Lite interface to data memory
- **Writeback:** Register file write with forwarding support

---

## 📁 Module Structure

### Core Modules

#### 1. **riscv_core.sv** - Top-Level Core
**Status:** ✅ Complete  
**Purpose:** Main core integration and pipeline coordination

**Key Features:**
- Pipeline stage instantiation and interconnection
- Hazard unit integration
- AXI4 interface management
- Clock and reset distribution

**Interfaces:**
- AXI4-Lite instruction memory interface
- AXI4-Lite data memory interface
- System clock and reset

#### 2. **fetch_stage.sv** - Instruction Fetch
**Status:** ✅ Complete  
**Purpose:** Instruction fetching and PC management

**Key Features:**
- Program counter management
- AXI4-Lite instruction fetch
- Branch target calculation
- Pipeline register interface

**Future Enhancements:**
- Branch prediction unit integration
- Instruction cache integration
- Prefetch buffer

#### 3. **decode_stage.sv** - Instruction Decode
**Status:** ✅ Complete  
**Purpose:** Instruction decoding and control signal generation

**Key Features:**
- RV32IM instruction decoding
- Control signal generation
- Register file read
- Immediate value generation
- Hazard detection interface

**Supported Instructions:**
- **RV32I:** All base integer instructions
- **RV32M:** MUL, MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU

#### 4. **execute_stage.sv** - Execute
**Status:** ✅ Complete  
**Purpose:** ALU operations, multiplication, division, and branching

**Key Features:**
- ALU with overflow detection
- Multi-cycle multiplier unit
- Multi-cycle divider unit
- Branch logic and target calculation
- Forwarding logic integration
- Stall request generation

**Functional Units:**
- **ALU:** Arithmetic, logical, shift, comparison operations
- **Multiplier:** RV32M multiplication instructions
- **Divider:** RV32M division instructions
- **Branch Unit:** Conditional and unconditional branches

#### 5. **mem_stage.sv** - Memory Access
**Status:** ✅ Complete  
**Purpose:** Memory operations and AXI4 interface

**Key Features:**
- Load/store operations
- AXI4-Lite data memory interface
- Memory alignment handling
- Pipeline register management

#### 6. **writeback_stage.sv** - Writeback
**Status:** ✅ Complete  
**Purpose:** Register file write and result forwarding

**Key Features:**
- Register file write operations
- Result forwarding to earlier stages
- Pipeline completion

### Functional Units

#### 7. **alu.sv** - Arithmetic Logic Unit
**Status:** ✅ Complete  
**Purpose:** Integer arithmetic and logical operations

**Key Features:**
- All RV32I ALU operations
- Overflow detection for ADD/SUB
- Zero flag generation
- Signed/unsigned operations

**Operations:**
- **Arithmetic:** ADD, SUB, LUI, AUIPC
- **Logical:** AND, OR, XOR
- **Shifts:** SLL, SRL, SRA
- **Comparisons:** SLT, SLTU

#### 8. **mult_unit.sv** - Multiplication Unit
**Status:** ✅ Complete  
**Purpose:** RV32M multiplication operations

**Key Features:**
- Multi-cycle multiplication
- All RV32M multiplication types
- Configurable operation types
- Done signal generation

**Operations:**
- **MUL:** Signed × Signed (lower 32 bits)
- **MULH:** Signed × Signed (upper 32 bits)
- **MULHSU:** Signed × Unsigned (upper 32 bits)
- **MULHU:** Unsigned × Unsigned (upper 32 bits)

#### 9. **div_unit.sv** - Division Unit
**Status:** ✅ Complete  
**Purpose:** RV32M division operations

**Key Features:**
- Multi-cycle division
- All RV32M division types
- Exception handling (division by zero, overflow)
- Done signal generation

**Operations:**
- **DIV:** Signed division
- **DIVU:** Unsigned division
- **REM:** Signed remainder
- **REMU:** Unsigned remainder

#### 10. **reg_file.sv** - Register File
**Status:** ✅ Complete  
**Purpose:** 32x32 general-purpose register file

**Key Features:**
- Dual read ports
- Single write port
- Register x0 hardwired to zero
- Hazard detection support

#### 11. **csr_regfile.sv** - Control and Status Registers
**Status:** ✅ Complete  
**Purpose:** RISC-V control and status registers

**Key Features:**
- Basic CSR operations
- Machine mode support
- Exception handling registers
- Interrupt control

### Control and Hazard Management

#### 12. **hazard_unit.sv** - Hazard Detection and Resolution
**Status:** ✅ Complete  
**Purpose:** Pipeline hazard detection and forwarding

**Key Features:**
- Data hazard detection
- Load-use hazard detection
- Forwarding logic (EX/MEM → EX, MEM/WB → EX)
- Pipeline stall generation
- Branch hazard handling

**Hazard Types Handled:**
- **RAW Hazards:** Register read-after-write
- **Load-Use Hazards:** Load followed by dependent instruction
- **Control Hazards:** Branch and jump instructions
- **Structural Hazards:** Multi-cycle operations

---

## 🔧 Implementation Details

### Pipeline Registers

#### IF/ID Register
```systemverilog
typedef struct packed {
    addr_t         pc;
    word_t         instruction;
    logic          valid;
} if_id_reg_t;
```

#### ID/EX Register
```systemverilog
typedef struct packed {
    addr_t         pc;
    word_t         rs1_data;
    word_t         rs2_data;
    word_t         immediate;
    reg_addr_t     rs1_addr;
    reg_addr_t     rs2_addr;
    reg_addr_t     rd_addr;
    ctrl_signals_t ctrl;
    logic          valid;
} id_ex_reg_t;
```

#### EX/MEM Register
```systemverilog
typedef struct packed {
    word_t         alu_result;
    word_t         store_data;
    reg_addr_t     rd_addr;
    logic          alu_overflow;
    ctrl_signals_t ctrl;
} ex_mem_reg_t;
```

#### MEM/WB Register
```systemverilog
typedef struct packed {
    word_t         result;
    reg_addr_t     rd_addr;
    logic          reg_write_en;
} mem_wb_reg_t;
```

### Control Signals
```systemverilog
typedef struct packed {
    // ALU Control
    alu_op_t       alu_op;
    logic          alu_src_a_sel;
    logic          alu_src_b_sel;
    
    // Memory Control
    logic          mem_read_en;
    logic          mem_write_en;
    logic [1:0]    mem_size;
    
    // Register Control
    logic          reg_write_en;
    wb_mux_sel_t   wb_mux_sel;
    
    // Branch Control
    logic          branch_en;
    logic          jump_en;
    
    // Multiplier/Divider Control
    logic          mult_en;
    logic          div_en;
    
    // CSR Control
    logic          csr_read_en;
    logic          csr_write_en;
} ctrl_signals_t;
```

---

## 📊 Performance Characteristics

### Current Performance Metrics
| Metric | Value | Notes |
|--------|-------|-------|
| **IPC (Instructions Per Cycle)** | ~0.8 | Typical for 5-stage pipeline |
| **Branch Prediction** | Not implemented | Always predict not-taken |
| **Cache** | Not implemented | Direct memory access |
| **Pipeline Efficiency** | ~70% | Due to hazards and stalls |
| **Clock Frequency** | Target: 100MHz | Depends on synthesis |

### Pipeline Hazards Impact
| Hazard Type | Frequency | Impact | Mitigation |
|-------------|-----------|--------|------------|
| **Data Hazards** | High | 2-3 cycle penalty | Forwarding logic |
| **Load-Use Hazards** | Medium | 1 cycle penalty | Pipeline stall |
| **Control Hazards** | Medium | 2-3 cycle penalty | Branch resolution |
| **Structural Hazards** | Low | Variable penalty | Multi-cycle units |

---

## 🔍 Verification Status

### Functional Verification
- [x] **RV32I Base Instructions:** All instructions verified
- [x] **RV32M Multiplication:** All multiplication types verified
- [x] **RV32M Division:** All division types verified
- [x] **Hazard Handling:** Data hazards and forwarding verified
- [x] **Branch Instructions:** Conditional and unconditional branches verified
- [x] **Memory Operations:** Load/store operations verified
- [x] **CSR Operations:** Basic CSR read/write verified

### Performance Verification
- [x] **Pipeline Stalls:** Correct stall behavior verified
- [x] **Forwarding Logic:** Data forwarding verified
- [x] **Multi-cycle Operations:** Multiplier and divider timing verified
- [x] **Exception Handling:** Basic exception detection verified

### Interface Verification
- [x] **AXI4-Lite Protocol:** Instruction and data interfaces verified
- [x] **Memory Alignment:** Proper alignment handling verified
- [x] **Reset Behavior:** Correct reset and initialization verified

---

## 🚀 Current Capabilities

### Supported Instruction Set
#### RV32I Base Integer Instructions
- **Arithmetic:** ADD, ADDI, SUB, LUI, AUIPC
- **Logical:** AND, ANDI, OR, ORI, XOR, XORI
- **Shifts:** SLL, SLLI, SRL, SRLI, SRA, SRAI
- **Comparisons:** SLT, SLTI, SLTU, SLTIU
- **Branches:** BEQ, BNE, BLT, BGE, BLTU, BGEU
- **Jumps:** JAL, JALR
- **Memory:** LB, LH, LW, LBU, LHU, SB, SH, SW

#### RV32M Multiplication and Division
- **Multiplication:** MUL, MULH, MULHSU, MULHU
- **Division:** DIV, DIVU, REM, REMU

### System Features
- **Privilege Level:** Machine mode (M-mode)
- **Exception Handling:** Basic exception detection
- **Interrupt Support:** Basic interrupt framework
- **Memory Interface:** AXI4-Lite compatible
- **Reset Strategy:** Asynchronous reset, synchronous de-assertion

---

## 🔧 Synthesis and Implementation

### Target Technology
- **FPGA:** Xilinx 7-series, Intel Cyclone V
- **ASIC:** 28nm and below
- **Clock Frequency:** 100MHz target
- **Area:** Optimized for embedded applications

### Resource Utilization (Estimated)
| Resource | Count | Notes |
|----------|-------|-------|
| **LUTs** | ~5K-8K | Depends on configuration |
| **FFs** | ~2K-3K | Pipeline registers and state |
| **BRAMs** | 2-4 | Register file and potential caches |
| **DSPs** | 0 | Multiplier/divider in fabric |

### Timing Constraints
- **Critical Path:** ALU → Pipeline Register
- **Setup Time:** 2ns (100MHz target)
- **Hold Time:** 0.5ns
- **Clock-to-Q:** 1ns

---

## 📝 Known Limitations

### Current Limitations
1. **No Branch Prediction:** Always predict not-taken
2. **No Instruction Cache:** Direct memory access
3. **No Data Cache:** Direct memory access
4. **Basic Exception Handling:** Limited exception types
5. **Single Issue:** No superscalar execution
6. **No Out-of-Order Execution:** In-order pipeline only

### Performance Bottlenecks
1. **Memory Access Latency:** No caching
2. **Branch Penalties:** No prediction
3. **Pipeline Stalls:** Due to hazards
4. **Multi-cycle Operations:** Multiplier/divider stalls

---

## 🔄 Future Enhancement Path

### Phase 1 Improvements (Planned)
- [ ] **Branch Prediction Unit:** 2-bit saturating counter with BTB
- [ ] **Instruction Cache:** 4KB, 2-way set associative
- [ ] **Enhanced Exception Handling:** Complete RISC-V M-mode support

### Phase 2 Improvements (Future)
- [ ] **Data Cache:** Write-back cache with coherency
- [ ] **Advanced Branch Prediction:** Global history predictor
- [ ] **Instruction-Level Parallelism:** Multiple execution units

### Phase 3 Improvements (Future)
- [ ] **Superscalar Execution:** Multiple instructions per cycle
- [ ] **Out-of-Order Execution:** Dynamic scheduling
- [ ] **Advanced Memory Hierarchy:** Multi-level cache system

---

## 📚 Documentation and Resources

### Design Documents
- [Phase 1 Improvements Roadmap](PHASE1_IMPROVEMENTS.md)
- [RISC-V Specification](https://riscv.org/specifications/)
- [Pipeline Architecture Reference](https://en.wikipedia.org/wiki/Classic_RISC_pipeline)

### Verification Resources
- [RISC-V Compliance Tests](https://github.com/riscv/riscv-compliance)
- [RISC-V Formal Verification](https://github.com/riscv/riscv-formal)
- [RISC-V Test Suite](https://github.com/riscv/riscv-tests)

---

## 🎯 Summary

The current RISC-V core implementation provides a solid foundation with:

### ✅ **Strengths**
- **Complete RV32IM Support:** All required instructions implemented
- **Robust Pipeline:** 5-stage pipeline with comprehensive hazard handling
- **Industry-Standard Interfaces:** AXI4-Lite memory interfaces
- **Synthesizable Design:** Clean, lint-free RTL code
- **Comprehensive Verification:** All major functions verified

### 🔧 **Ready for Enhancement**
- **Modular Architecture:** Easy to add new features
- **Clear Interfaces:** Well-defined module boundaries
- **Extensible Design:** Support for future enhancements
- **Documentation:** Complete implementation documentation

### 🚀 **Next Steps**
The core is ready for Phase 1 improvements, starting with branch prediction and instruction caching to achieve significant performance improvements while maintaining the solid foundation already established.

---

**Document Version:** 1.0  
**Last Updated:** 2025-06-28  
**Core Version:** 1.2.0  
**Status:** Production Ready
