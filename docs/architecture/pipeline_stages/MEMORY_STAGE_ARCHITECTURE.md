# Memory Stage (M) Architecture

## 1. Overview

The Memory Stage (M) is the fourth stage of the RISC-V pipeline. Its primary responsibilities include performing load and store operations to the data memory, handling data alignment for byte and half-word accesses, and passing results to the Writeback stage.

## 2. Key Components and Data Flow

### 2.1. Conceptual Block Diagram

```
┌───────────────────────────────────────────────────────────────────────────┐
│                                 Memory Stage (M)                          │
│                                                                           │
│  ┌───────────────────┐     ┌───────────────────┐     ┌───────────────────┐
│  │                   │     │                   │     │                   │
│  │  EX/MEM Register  │     │ Write Data        │     │  Read Data        │
│  │ (Input from Execute)│     │ Alignment         │     │  Alignment        │
│  └─────────┬─────────┘     └─────────┬─────────┘     └─────────┬─────────┘
│            │                         │                         │
│            ▼                         ▼                         ▼
│  ┌───────────────────────────────────────────────────────────────────┐
│  │                       Memory Wrapper Interface Control          │
│  │ (Data Request/Response)                                         │
│  └─────────┬─────────────────────────────────────────────────────────┘
│            │                                                            │
│            ▼                                                            │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  Memory Exception │                                                  │
│  │  Detection        │                                                  │
│  └─────┬─────┬───────┘                                                  │
│        │     │                                                          │
│        ▼     ▼                                                          │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  MEM/WB Register  │                                                  │
│  │ (Output to Writeback)│                                                  │
│  └───────────────────┘                                                  │
└───────────────────────────────────────────────────────────────────────────┘
```

### 2.2. Component Descriptions

-   **EX/MEM Register**: This pipeline register (`ex_mem_reg_i`) receives the ALU result, store data, and control signals from the Execute stage.
-   **Write Data Alignment Logic**: For store instructions, this logic shifts the data to the correct byte lanes and generates appropriate write strobes based on the address and access size.
-   **Read Data Alignment Logic**: For load instructions, this logic extracts the correct byte or half-word from the 32-bit memory response and performs sign- or zero-extension.
-   **Memory Wrapper Interface Control**: Drives the signals for the memory wrapper (e.g., `data_req_valid_o`, `data_req_addr_o`, `data_req_write_o`, `data_req_data_o`, `data_req_strb_o`, `data_req_size_o`) to perform memory accesses.
-   **Memory Exception Detection**: Identifies memory-related exceptions such as load/store address misalignment and load/store access faults.
-   **MEM/WB Register**: This pipeline register (`mem_wb_reg_o`) latches the final write-back data, destination register address, and control signals, passing them to the Writeback stage.

## 3. Detailed Logic Flow

### 3.1. Write Data Alignment

For `STORE` instructions, the `store_data` from the `ex_mem_reg_i` is aligned to the correct byte position within a word based on `alu_result[1:0]` (byte offset) and `funct3` (access size). The `write_strobes` are generated accordingly to enable writing only to the intended bytes.

### 3.2. Read Data Alignment

For `LOAD` instructions, the `data_rsp_data_i` (32-bit word from memory) is processed based on `alu_result[1:0]` (byte offset) and `funct3` (access size). The relevant bytes/half-words are extracted and then sign-extended (for LB, LH) or zero-extended (for LBU, LHU) to a 32-bit word (`read_data_aligned`).

### 3.3. Write-back Data Selection

The `wb_data_d` signal, which will be written back to the Register File in the Writeback stage, is selected:
-   If the instruction is a `LOAD` (`mem_read_en`), `wb_data_d` is `read_data_aligned`.
-   Otherwise, `wb_data_d` is the `alu_result` from the Execute stage (for R-type, I-type, U-type, J-type instructions).

### 3.4. Memory Wrapper Interface Control

-   **Request Generation**: `data_req_valid_o` is asserted if `mem_read_en` or `mem_write_en` is active. The `data_req_addr_o` is the `alu_result` (effective memory address). `data_req_write_o` indicates a store operation. `data_req_data_o` and `data_req_strb_o` are the aligned data and strobes for stores.
-   **Size Encoding**: `data_req_size_o` is derived from `funct3` to indicate the access size (byte, half-word, word) to the memory wrapper.
-   **Handshake**: The stage waits for `data_req_ready_i` before sending a request and `data_rsp_valid_i` for a response. `data_rsp_ready_o` is always asserted, indicating readiness to accept responses.

### 3.5. Memory Exception Detection

The Memory stage detects the following exceptions:
-   **Load/Store Address Misalignment**: Checks if the effective memory address (`alu_result`) is aligned to the access size (e.g., half-word access to an odd address, word access to a non-word-aligned address).
-   **Load/Store Access Fault**: Detected if the memory response indicates an error (`data_rsp_error_i` is high when `data_rsp_valid_i` is high).

These exceptions are prioritized with any exceptions passed from the Execute stage and propagated via `exception_o` to the central exception handler.

### 3.6. Pipeline Register (MEM/WB) Update

The `mem_wb_reg_q` (MEM/WB pipeline register) is updated on the positive clock edge:
-   **Reset**: On reset, it's initialized with NOP-like values.
-   **Stall**: If `stall_w_i` is asserted, the register holds its current value.
-   **Flush**: If `flush_m_i` is asserted, the register is loaded with NOP-like values, clearing the pipeline.
-   **Normal Operation**: Otherwise, it latches `wb_data_d`, `rd_addr`, `reg_write_en`, `wb_mux_sel`, and `exception_detected` information.

## 4. Implementation Nuances

-   **Combinational Logic**: The data alignment and memory interface control logic are primarily combinational for speed.
-   **Hazard Unit Interaction**: The Hazard Unit is crucial for stalling the pipeline until memory responses for loads are valid, preventing data hazards.
-   **Exception Propagation**: The Memory stage passes through exceptions from previous stages if no new memory-related exception is detected, maintaining the highest priority exception.

## 5. Interfaces

-   **`clk_i`, `rst_ni`**: System clock and reset.
-   **`stall_w_i`, `flush_m_i`**: Control signals from the Hazard Unit for pipeline control.
-   **`ex_mem_reg_i`**: Input pipeline register from the Execute stage.
-   **Memory Wrapper Data Interface**: `data_req_valid_o`, `data_req_ready_i`, `data_req_addr_o`, `data_req_write_o`, `data_req_size_o`, `data_req_data_o`, `data_req_strb_o`, `data_rsp_valid_i`, `data_rsp_ready_o`, `data_rsp_data_i`, `data_rsp_error_i` for communication with the memory wrapper/DCache.
-   **`mem_wb_reg_o`**: Output pipeline register to the Writeback stage.
-   **`exception_o`**: Output for detected exceptions.
