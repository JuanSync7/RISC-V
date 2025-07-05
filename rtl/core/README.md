# Core Pipeline Implementation

## Overview

This directory contains the core pipeline implementation of the RISC-V RV32IM processor. The pipeline consists of five stages: Fetch, Decode, Execute, Memory, and Writeback.

## Files

| File | Description |
|------|-------------|
| `riscv_core.sv` | Main core module that instantiates all pipeline stages |
| `riscv_core_pkg.sv` | Package containing core-wide definitions and types |
| `fetch_stage.sv` | Instruction fetch stage |
| `decode_stage.sv` | Instruction decode stage |
| `execute_stage.sv` | Execute stage with ALU operations and DPU integration |
| `fpu_unit.sv` | Floating Point Unit (FPU) |
| `vpu_unit.sv` | Vector Processing Unit (VPU) |
| `ml_inference_unit.sv` | Machine Learning Inference Unit (MLIU) |
| `mem_stage.sv` | Memory access stage |
| `writeback_stage.sv` | Writeback stage for register updates |

## Pipeline Architecture

### Stage Overview

```
┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐
│  Fetch  │───▶│ Decode  │───▶│Execute  │───▶│ Memory  │───▶│Writeback│
│  Stage  │    │  Stage  │    │ Stage   │    │  Stage  │    │  Stage  │
└─────────┘    └─────────┘    └─────────┘    └─────────┘    └─────────┘
```

### Stage Details

#### Fetch Stage (`fetch_stage.sv`)
- **Purpose**: Fetch instructions from memory
- **Key Functions**:
  - Program Counter (PC) management
  - Instruction memory access
  - Branch target calculation
  - Pipeline stall handling

#### Decode Stage (`decode_stage.sv`)
- **Purpose**: Decode instructions and read registers
- **Key Functions**:
  - Instruction decoding
  - Register file read access
  - Immediate value generation
  - Control signal generation

#### Execute Stage (`execute_stage.sv`)
- **Purpose**: Execute arithmetic and logical operations
- **Key Functions**:
  - ALU operations
  - Branch condition evaluation
  - Forwarding logic
  - Hazard detection

#### Memory Stage (`mem_stage.sv`)
- **Purpose**: Access data memory
- **Key Functions**:
  - Load/store operations
  - Memory address calculation
  - Memory access control
  - Cache interface

#### Writeback Stage (`writeback_stage.sv`)
- **Purpose**: Write results back to registers
- **Key Functions**:
  - Register file write access
  - Result multiplexing
  - Pipeline completion

## Pipeline Registers

Each stage communicates with the next stage through pipeline registers:

```systemverilog
typedef struct packed {
    logic [31:0] pc;
    logic [31:0] instruction;
    logic [31:0] data_a;
    logic [31:0] data_b;
    logic [31:0] immediate;
    alu_op_e alu_op;
    logic mem_read;
    logic mem_write;
    logic reg_write;
    logic [4:0] rd_addr;
} pipeline_reg_t;
```

## Hazard Handling

### Data Hazards
- **RAW (Read After Write)**: Handled by forwarding logic
- **WAW (Write After Write)**: Handled by register file design
- **WAR (Write After Read)**: Not possible in this pipeline

### Control Hazards
- **Branch Hazards**: Handled by branch prediction and flush
- **Exception Hazards**: Handled by exception handler

## Forwarding Logic

The forwarding logic routes data from later pipeline stages to earlier stages:

```systemverilog
// Forwarding multiplexers
always_comb begin
    if (forward_a == 2'b01) operand_a = ex_result;
    else if (forward_a == 2'b10) operand_a = mem_result;
    else operand_a = id_data_a;
end
```

## Performance Considerations

### Pipeline Efficiency
- **CPI (Cycles Per Instruction)**: Target < 1.2
- **Branch Prediction**: Static prediction (not-taken)
- **Cache Hit Rate**: Target > 95%

### Optimization Opportunities
- Dynamic branch prediction
- Instruction cache optimization
- Pipeline balancing
- Forwarding path optimization

## Usage

### Instantiation
```systemverilog
riscv_core core (
    .clk_i(clk),
    .rst_n_i(rst_n),
    .instr_req_o(instr_req),
    .instr_addr_o(instr_addr),
    .instr_rdata_i(instr_data),
    .instr_rvalid_i(instr_valid),
    .data_req_o(data_req),
    .data_addr_o(data_addr),
    .data_wdata_o(data_wdata),
    .data_we_o(data_we),
    .data_be_o(data_be),
    .data_rdata_i(data_rdata),
    .data_rvalid_i(data_valid)
);
```

### Configuration
```systemverilog
// Core parameters
parameter integer RESET_PC = 32'h80000000;
parameter integer INSTR_CACHE_SIZE = 4096;
parameter integer DATA_CACHE_SIZE = 4096;
```

## Testing

### Unit Tests
Each stage has corresponding unit tests in `tb/unit/core/`:
- `fetch_stage_tb.sv`
- `decode_stage_tb.sv`
- `execute_stage_tb.sv`
- `mem_stage_tb.sv`
- `writeback_stage_tb.sv`

### Integration Tests
Pipeline integration tests verify stage interactions:
- Data forwarding
- Hazard detection
- Pipeline stalls
- Exception handling

## Future Enhancements

### Phase 1: Performance Improvements
1. **Dynamic Branch Prediction**: Implement branch predictor
2. **Pipeline Optimization**: Reduce critical path
3. **Cache Optimization**: Improve cache performance

### Phase 2: Advanced Features
1. **Superscalar Execution**: Multiple instructions per cycle
2. **Out-of-Order Execution**: Dynamic instruction scheduling
3. **Speculative Execution**: Branch speculation

### Phase 3: System Integration
1. **Memory Management**: MMU and TLB support
2. **Debug Interface**: Hardware debug support
3. **Performance Monitoring**: Performance counters

## Dependencies

### Internal Dependencies
- `riscv_core_pkg.sv`: Core package definitions
- `units/alu.sv`: ALU for execute stage
- `units/reg_file.sv`: Register file
- `memory/icache.sv`: Instruction cache
- `control/hazard_unit.sv`: Hazard detection

### External Dependencies
- SystemVerilog 2012 or later
- Memory interfaces for instruction and data access

## Contributing

When modifying pipeline stages:

1. Maintain pipeline register consistency
2. Update hazard detection logic
3. Verify forwarding paths
4. Test with comprehensive testbenches
5. Update documentation
6. Check timing constraints 