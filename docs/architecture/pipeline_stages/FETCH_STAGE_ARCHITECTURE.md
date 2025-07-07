# Fetch Stage (F) Architecture

## 1. Overview

The Fetch Stage (F) is the first stage of the RISC-V pipeline, responsible for retrieving instructions from memory. Its primary functions include Program Counter (PC) management, handling control flow changes (branches, jumps, exceptions), interacting with the Instruction Cache (ICache), and passing the fetched instruction to the Decode stage.

## 2. Key Components and Data Flow

### 2.1. Conceptual Block Diagram

```
┌───────────────────────────────────────────────────────────────────────────┐
│                                 Fetch Stage (F)                           │
│                                                                           │
│  ┌───────────┐     ┌───────────────────┐     ┌───────────────────┐      │
│  │           │     │                   │     │                   │      │
│  │   PC      │     │  Branch Predictor │     │      ICache       │      │
│  │ Management│     │                   │     │                   │      │
│  │           │     │ (BTB, BHT)        │     │ (Instruction Cache) │      │
│  └─────┬─────┘     └─────────┬─────────┘     └─────────┬─────────┘      │
│        │                     │                         │                │
│        │                     │                         │                │
│        ▼                     ▼                         ▼                │
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │                       Next PC Selection Logic                     │  │
│  │ (Redirect, Prediction, PC+4)                                      │  │
│  └─────────┬─────────────────────────────────────────────────────────┘  │
│            │                                                            │
│            ▼                                                            │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  PC Register      │                                                  │
│  │                   │                                                  │
│  └─────┬─────┘                                                          │
│        │                                                                │
│        ▼                                                                │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  IF/ID Register   │                                                  │
│  │                   │                                                  │
│  └───────────────────┘                                                  │
│            │                                                            │
│            ▼                                                            │
│      To Decode Stage                                                    │
└───────────────────────────────────────────────────────────────────────────┘
```

### 2.2. Component Descriptions

-   **PC Management**: Handles the Program Counter (`pc_q`, `pc_d`) which points to the address of the instruction to be fetched. It updates based on sequential flow, branch predictions, or explicit redirects.
-   **Branch Predictor (`branch_predictor` instance)**: Provides predictions for conditional branches and targets for indirect jumps. It contains a Branch Target Buffer (BTB) and a Branch History Table (BHT) (though dynamic prediction is a future enhancement, the structures are present).
-   **ICache (`icache` instance)**: The Instruction Cache provides fast access to instructions. The Fetch stage sends instruction addresses to the ICache and receives fetched instructions.
-   **Next PC Selection Logic**: This combinational logic determines the address of the next instruction to be fetched based on a priority scheme.
-   **PC Register**: A sequential element that holds the current Program Counter value.
-   **IF/ID Register**: A pipeline register that latches the fetched instruction and its PC, passing them to the Decode stage.

## 3. Detailed Logic Flow

### 3.1. Program Counter (PC) Update Logic

The `pc_d` (next PC) is determined by a prioritized selection:
1.  **PC Redirect**: Highest priority. If `pc_redirect_en_i` is asserted (from a taken branch, jump, or exception in a later stage), `pc_d` is set to `pc_redirect_target_i`.
2.  **Branch Prediction**: If no redirect, and the `branch_predictor` predicts a taken branch (`bp_predict_taken` and `bp_btb_hit`), `pc_d` is set to `bp_predict_target`.
3.  **Sequential Execution**: Default. If neither of the above conditions is met, `pc_d` is simply `pc_q + 4` (for 32-bit instructions).

The `pc_q` (current PC) register is updated on the positive clock edge, unless the `stall_f_i` signal is asserted, which freezes the PC.

### 3.2. Instruction Fetch and ICache Interaction

-   The `pc_q` is provided to the `icache` module as the instruction address (`pc_i`).
-   The `icache` returns the fetched `instruction_o` and `valid_o` signals.
-   The `fetch_stage` asserts `instr_req_valid_o` to the memory wrapper (via ICache) when it needs a new instruction and is not stalled.
-   It waits for `instr_req_ready_i` from the memory wrapper and `instr_rsp_valid_i` with `instr_rsp_data_i` for the fetched instruction.

### 3.3. Pipeline Register (IF/ID) Update

The `if_id_reg_q` (IF/ID pipeline register) is updated on the positive clock edge:
-   **Reset**: On reset, it's initialized with a NOP instruction and invalid PC.
-   **Stall**: If `stall_d_i` is asserted, the register holds its current value, preventing new data from entering the Decode stage.
-   **Flush**: If `flush_f_i` is asserted, the register is loaded with a NOP instruction, effectively injecting a bubble into the pipeline.
-   **Normal Operation**: Otherwise, it latches the `icache_instruction` and `pc_q` (current PC) from the Fetch stage.

### 3.4. Exception Detection

The Fetch stage detects two types of exceptions:
-   **Instruction Address Misalignment**: Occurs if the `pc_q` is not 2-byte aligned (i.e., `pc_q[0]` is high). This is a RISC-V requirement.
-   **Instruction Access Fault**: Occurs if the instruction memory response indicates an error (`instr_rsp_error_i` is high when `instr_rsp_valid_i` is high).

These detected exceptions are propagated via the `exception_o` port to the central exception handler.

## 4. Implementation Nuances

-   **Static Branch Prediction**: Currently, the `branch_predictor` primarily supports static not-taken prediction. The dynamic prediction logic (BHT updates, complex BTB lookups) is a planned enhancement.
-   **RVC Instruction Support (Future)**: The current PC increment is fixed at +4. For RVC support, this logic will need to be updated to dynamically increment by 2 or 4 bytes based on the instruction's LSBs.
-   **Performance Counters**: The module includes ports for performance counters related to ICache hits/misses and flushes, allowing for detailed performance analysis.

## 5. Interfaces

-   **`clk_i`, `rst_ni`**: System clock and reset.
-   **`stall_f_i`, `stall_d_i`, `flush_f_i`**: Control signals from the Hazard Unit for pipeline control.
-   **`pc_redirect_en_i`, `pc_redirect_target_i`**: Inputs for PC redirection from later pipeline stages.
-   **`bp_update_i`**: Input for branch prediction updates from the Execute stage.
-   **Instruction Memory Interface**: `instr_req_valid_o`, `instr_req_ready_i`, `instr_req_addr_o`, `instr_rsp_valid_i`, `instr_rsp_ready_o`, `instr_rsp_data_i`, `instr_rsp_error_i` for communication with the memory wrapper/ICache.
-   **`if_id_reg_o`**: Output pipeline register to the Decode stage.
-   **`pc_f_o`**: Current PC value output.
-   **`bp_prediction_o`**: Branch prediction result output.
-   **`exception_o`**: Output for detected exceptions.
-   **Performance Counter Ports**: `perf_hit_count_o`, `perf_miss_count_o`, etc.
