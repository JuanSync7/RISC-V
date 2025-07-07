# Writeback Stage (W) Architecture

## 1. Overview

The Writeback Stage (W) is the final stage of the RISC-V pipeline. It is a purely combinational stage responsible for writing the final computed result back to the Register File. It also provides the necessary data and control signals for data forwarding to earlier pipeline stages.

## 2. Key Components and Data Flow

### 2.1. Conceptual Block Diagram

```
┌───────────────────────────────────────────────────────────────────────────┐
│                                 Writeback Stage (W)                       │
│                                                                           │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  MEM/WB Register  │                                                  │
│  │ (Input from Memory)│                                                  │
│  └─────────┬─────────┘                                                  │
│            │                                                            │
│            ▼                                                            │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  Register File    │                                                  │
│  │  Write Port       │                                                  │
│  └─────┬─────┬───────┘                                                  │
│        │     │                                                          │
│        ▼     ▼                                                          │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  Forwarding Unit  │                                                  │
│  │  Feedback         │                                                  │
│  └───────────────────┘                                                  │
└───────────────────────────────────────────────────────────────────────────┘
```

### 2.2. Component Descriptions

-   **MEM/WB Register**: This pipeline register (`mem_wb_reg_i`) receives the final result (`wb_data`), destination register address (`rd_addr`), and write enable signal (`reg_write_en`) from the Memory stage.
-   **Register File Write Port**: The Writeback stage drives the inputs to the Register File's write port (`write_en_o`, `rd_addr_o`, `rd_data_o`) to update the architectural state.
-   **Forwarding Unit Feedback**: It provides the result and destination register information (`wb_data_fwd_o`, `rd_addr_fwd_o`, `reg_write_en_fwd_o`) back to the Execute stage for data forwarding, enabling the resolution of Read-After-Write (RAW) hazards.

## 3. Detailed Logic Flow

### 3.1. Register File Write Operation

The Writeback stage is primarily a pass-through stage. The signals for the Register File write port are directly assigned from the values latched in the `mem_wb_reg_i`:
-   `write_en_o` is assigned `mem_wb_reg_i.reg_write_en`.
-   `rd_addr_o` is assigned `mem_wb_reg_i.rd_addr`.
-   `rd_data_o` is assigned `mem_wb_reg_i.wb_data`.

These signals are then connected to the `reg_file` instance at the top level of the `riscv_core.sv` module.

### 3.2. Forwarding Path Generation

To support data forwarding, the Writeback stage provides its output data and destination register information back to the Execute stage:
-   `wb_data_fwd_o` is assigned `mem_wb_reg_i.wb_data`.
-   `rd_addr_fwd_o` is assigned `mem_wb_reg_i.rd_addr`.
-   `reg_write_en_fwd_o` is assigned `mem_wb_reg_i.reg_write_en`.

This feedback path allows the Execute stage to bypass the Register File and directly use the result of an instruction that is still in the Memory or Writeback stage, thereby reducing stalls due to data dependencies.

## 4. Implementation Nuances

-   **Combinational Stage**: The Writeback stage is entirely combinational. It does not contain any sequential logic (flip-flops) itself, as its primary role is to prepare and present data for the Register File write and forwarding paths.
-   **Architectural State Update**: This is the point where the architectural state of the processor (the contents of the general-purpose registers) is officially updated.
-   **Simplicity**: Due to its combinational nature and direct pass-through logic, the Writeback stage is typically the simplest stage in a classic 5-stage pipeline.

## 5. Interfaces

-   **`clk_i`, `rst_ni`**: System clock and reset (though not directly used by combinational logic, included for module consistency).
-   **`mem_wb_reg_i`**: Input pipeline register from the Memory stage.
-   **Outputs to Register File**: `write_en_o`, `rd_addr_o`, `rd_data_o`.
-   **Outputs for Forwarding Unit**: `wb_data_fwd_o`, `rd_addr_fwd_o`, `reg_write_en_fwd_o`.
