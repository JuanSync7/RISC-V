# Hazard Unit Architecture

## 1. Overview

The Hazard Unit is a purely combinational module responsible for detecting and resolving pipeline hazards in the RISC-V core. It generates stall, flush, and forwarding control signals to ensure correct program execution by preventing data and control hazards.

## 2. Key Components and Data Flow

### 2.1. Conceptual Block Diagram

```
┌───────────────────────────────────────────────────────────────────────────┐
│                                 Hazard Unit                               │
│                                                                           │
│  ┌───────────────────┐     ┌───────────────────┐     ┌───────────────────┐
│  │                   │     │                   │     │                   │
│  │ Pipeline Register │     │   Hazard          │     │   Stall / Flush   │
│  │ State Inputs      │     │   Detection Logic │     │   Generation      │
│  │                   │     │                   │     │                   │
│  └─────────┬─────────┘     └─────────┬─────────┘     └─────────┬─────────┘
│            │                         │                         │
│            ▼                         ▼                         ▼
│  ┌───────────────────────────────────────────────────────────────────┐
│  │                       Forwarding Logic                            │
│  │ (EX/MEM -> EX, MEM/WB -> EX)                                      │
│  └─────────┬─────────────────────────────────────────────────────────┘
│            │                                                            │
│            ▼                                                            │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │ Pipeline Control  │                                                  │
│  │ Outputs           │                                                  │
│  └───────────────────┘                                                  │
└───────────────────────────────────────────────────────────────────────────┘
```

### 2.2. Component Descriptions

-   **Pipeline Register State Inputs**: The Hazard Unit receives critical information from the ID/EX, EX/MEM, and MEM/WB pipeline registers, including register addresses (`rs1_addr_d_i`, `rs2_addr_d_i`, `id_ex_reg_i.rd_addr`, `ex_mem_reg_i.rd_addr`, `mem_wb_reg_i.rd_addr`) and write enable signals (`id_ex_reg_i.ctrl.mem_read_en`, `ex_mem_reg_i.ctrl.reg_write_en`, `mem_wb_reg_i.reg_write_en`).
-   **Control and Status Inputs**: Additional inputs include PC redirect signals (`pc_redirect_e_i`), stall requests from multi-cycle units (`exec_stall_req_i`), and memory handshake signals (`i_arvalid_i`, `i_arready_i`, `d_mem_req_i`, `d_mem_ready_i`).
-   **Hazard Detection Logic**: Combinational logic that identifies various hazard conditions based on the input signals.
-   **Stall/Flush Generation**: Logic that asserts appropriate stall (`stall_f_o`, `stall_d_o`, `stall_m_o`, `stall_w_o`) and flush (`flush_f_o`, `flush_d_o`, `flush_e_o`) signals to control the pipeline flow.
-   **Forwarding Logic**: Determines the source of operands for the Execute stage (`forward_a_sel_o`, `forward_b_sel_o`) to bypass the Register File when data is available from later pipeline stages.

## 3. Detailed Logic Flow

### 3.1. Hazard Detection

-   **Load-Use Hazard**: Detected when an instruction in the Decode stage (`rs1_addr_d_i` or `rs2_addr_d_i`) attempts to read a register that is the destination of a LOAD instruction currently in the Execute stage (`id_ex_reg_i.ctrl.mem_read_en` and `id_ex_reg_i.rd_addr`). This hazard cannot be resolved by forwarding alone.
-   **Multi-cycle Execution Stall**: Signaled by the Execute stage (`exec_stall_req_i`) when a multi-cycle operation (e.g., multiplication, division, DPU operation) is in progress and not yet complete.
-   **Instruction Memory Wait Stall**: Occurs if the Fetch stage sends an instruction request (`i_arvalid_i`) but the instruction memory is not ready (`!i_arready_i`).
-   **Data Memory Wait Stall**: Occurs if the Memory stage sends a data memory request (`d_mem_req_i`) but the data memory is not ready (`!d_mem_ready_i`).

### 3.2. Stall Signal Generation and Propagation

Stall signals propagate backwards through the pipeline:
-   `stall_w_o`: The Writeback stage typically never stalls, so this is usually `1'b0`.
-   `stall_m_o`: Asserted if there's a `d_mem_wait_stall`.
-   `stall_e`: An internal signal that combines `stall_m_o` and `m_ext_stall` (from `exec_stall_req_i`).
-   `stall_d_o`: Asserted if `stall_e` or `load_use_hazard` is present.
-   `stall_f_o`: Asserted if `stall_d_o` or `i_mem_wait_stall` is present.

### 3.3. Flush Signal Generation

-   **Control Hazard Flush**: If a PC redirect (`pc_redirect_e_i`) is asserted (indicating a taken branch, jump, or exception), `flush_f_o` and `flush_d_o` are asserted. This flushes the instructions in the Fetch and Decode stages that were incorrectly fetched.
-   **Load-Use Hazard Bubble**: To resolve a load-use hazard, `flush_e_o` is asserted. This injects a bubble (NOP) into the Execute stage, giving the load instruction time to complete and its data to become available for forwarding.

### 3.4. Forwarding Logic

The forwarding logic determines which pipeline stage provides the correct operand data to the Execute stage, prioritizing the most recent valid data:

-   **EX/MEM -> EX Path (Highest Priority)**: If the instruction in the EX/MEM stage (`ex_mem_reg_i`) will write to a register that is an operand for the instruction in the ID/EX stage (`id_ex_reg_i`), and that register is not x0, then `forward_a_sel_o` or `forward_b_sel_o` is set to `FWD_SEL_MEM`.
-   **MEM/WB -> EX Path**: If the instruction in the MEM/WB stage (`mem_wb_reg_i`) will write to a register that is an operand for the instruction in the ID/EX stage, and that register is not x0, and the EX/MEM stage is *not* forwarding that operand, then `forward_a_sel_o` or `forward_b_sel_o` is set to `FWD_SEL_WB`.
-   **Default**: If no forwarding is needed or possible, the operand is read from the Register File (`FWD_SEL_REG`).

## 4. Implementation Nuances

-   **Combinational Design**: The Hazard Unit is purely combinational, meaning its outputs react immediately to changes in its inputs. This is crucial for fast hazard detection and resolution.
-   **Prioritization**: The logic for stall and flush generation, as well as forwarding, is carefully prioritized to ensure correct behavior in complex scenarios.
-   **Interaction with Pipeline Stages**: The Hazard Unit acts as the central control point for pipeline flow, receiving status from and sending control signals to all pipeline stages.

## 5. Interfaces

-   **Pipeline Register State Inputs**:
    -   `rs1_addr_d_i`, `rs2_addr_d_i`: Source register addresses from the Decode stage.
    -   `id_ex_reg_i`: State of the ID/EX pipeline register.
    -   `ex_mem_reg_i`: State of the EX/MEM pipeline register.
    -   `mem_wb_reg_i`: State of the MEM/WB pipeline register.
-   **Control and Status Inputs**:
    -   `pc_redirect_e_i`: PC redirect signal from the Execute stage.
    -   `exec_stall_req_i`: Stall request from multi-cycle units in the Execute stage.
    -   `i_arvalid_i`, `i_arready_i`: Instruction memory handshake signals.
    -   `d_mem_req_i`, `d_mem_ready_i`: Data memory handshake signals.
-   **Pipeline Control Outputs**:
    -   `stall_f_o`, `stall_d_o`, `stall_m_o`, `stall_w_o`: Stall signals for each pipeline stage.
    -   `flush_f_o`, `flush_d_o`, `flush_e_o`: Flush signals for each pipeline stage.
    -   `forward_a_sel_o`, `forward_b_sel_o`: Forwarding select signals for the Execute stage.
