# Out-of-Order (OoO) Execution Architecture

## 1. Overview
This document describes the architecture of the Out-of-Order (OoO) execution engine within the RISC-V core. OoO execution is a microarchitectural technique that allows a processor to execute instructions in an order different from their original program order, thereby improving instruction-level parallelism (ILP) and overall performance by hiding latencies (e.g., memory access, long-latency operations).

## 2. Key Components of the OoO Engine

The OoO engine typically consists of several interconnected components that manage instruction flow, data dependencies, and resource allocation:

### 2.1. Instruction Fetch and Decode
- Instructions are fetched and decoded in program order.
- Decoded instructions are then dispatched to the Reservation Stations.

### 2.2. Reservation Stations (`rtl/execution/reservation_station.sv`)
- **Purpose**: Buffers instructions that have been decoded but are waiting for their operands to become available or for a functional unit to become free. It is a key component for enabling out-of-order execution.
- **Internal Structure and Data Flow**:

```
┌───────────────────────────────────────────────────────────────────────────┐
│                                 Reservation Station (RS)                  │
│                                                                           │
│  ┌───────────────────┐     ┌───────────────────┐     ┌───────────────────┐
│  │                   │     │                   │     │                   │
│  │  Dispatch Inputs  │     │   RS Entries      │     │  Result Forwarding│
│  │ (New Instruction) │     │ (Storage Array)   │     │  (from CDB)       │
│  └─────────┬─────────┘     └─────────┬─────────┘     └─────────┬─────────┘
│            │                         │                         │
│            ▼                         ▼                         ▼
│  ┌───────────────────────────────────────────────────────────────────┐
│  │                       Issue Selection Logic                     │
│  │ (Finds ready instructions to issue)                             │
│  └─────────┬─────────────────────────────────────────────────────────┘
│            │                                                            │
│            ▼                                                            │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  Issue Outputs    │                                                  │
│  │ (To Functional Units)│                                                  │
│  └───────────────────┘                                                  │
└───────────────────────────────────────────────────────────────────────────┘
```

- **Functionality**:
    - **RS Entries**: A storage array (`rs_r`) that holds dispatched instructions. Each entry (`rs_entry_t`) contains the instruction's opcode, operand values (`v_rs1`, `v_rs2`), flags indicating if operands are waiting for results (`q_rs1_valid`, `q_rs2_valid`), the ROB tags of the operands (`q_rs1`, `q_rs2`), and the ROB tag of the instruction itself (`rob_tag`).
    - **Dispatch Logic**: When a new instruction is dispatched (`dispatch_valid_i`), the RS allocates a free entry (`alloc_ptr_r`) and stores the instruction's details. `dispatch_ready_o` indicates if there is space available in the RS.
    - **Result Forwarding**: The RS continuously monitors the Common Data Bus (CDB) via `result_valid_i` and `result_rob_tag_i`. If a broadcasted result matches an operand's ROB tag in any RS entry, that operand's `q_valid` flag is cleared, and its `v_rs` field is updated with the actual data. This resolves RAW hazards.
    - **Issue Selection Logic**: A combinational priority encoder (`issue_idx_c`) scans the RS entries to find the first instruction that is `busy` and has both its operands `ready` (i.e., `q_rs1_valid` and `q_rs2_valid` are false). This instruction is then marked as `issue_valid_o`.
    - **Issue Logic**: When `issue_valid_o` is asserted and the functional unit is `issue_ready_i`, the instruction's details (`issue_opcode_o`, `issue_v_rs1_o`, `issue_v_rs2_o`, `issue_rob_tag_o`) are sent to the functional units, and the RS entry is freed.
- **Implementation Nuances**:
    - **`rs_entry_t`**: A packed struct defining the contents of each reservation station entry.
    - **Circular Buffer (Implicit)**: While not explicitly using head/tail pointers like an ROB, the `alloc_ptr_r` and `issue_idx_c` effectively manage the circular nature of the RS entries.
    - **Simultaneous Dispatch and Issue**: The logic handles cases where an entry is issued and freed in the same cycle, allowing a new instruction to be dispatched to that newly freed slot.
    - **Flush Handling**: On a flush signal (`flush_i`), all entries in the RS are cleared, discarding speculative instructions.

### 2.3. Reorder Buffer (ROB) (`rtl/execution/reorder_buffer.sv`)
- **Purpose**: Maintains program order for instructions, even if they execute out of order. It is crucial for precise exceptions and correct architectural state updates.
- **Internal Structure and Data Flow**:

```
┌───────────────────────────────────────────────────────────────────────────┐
│                                 Reorder Buffer (ROB)                      │
│                                                                           │
│  ┌───────────────────┐     ┌───────────────────┐     ┌───────────────────┐
│  │                   │     │                   │     │                   │
│  │  Dispatch Inputs  │     │   ROB Entries     │     │  Execution Result │
│  │ (New Instruction) │     │ (Circular Buffer) │     │  Inputs (from CDB)│
│  └─────────┬─────────┘     └─────────┬─────────┘     └─────────┬─────────┘
│            │                         │                         │
│            ▼                         ▼                         ▼
│  ┌───────────────────────────────────────────────────────────────────┐
│  │                       Head/Tail Pointer Logic                   │
│  │ (Manages circular buffer, entry count)                          │
│  └─────────┬─────────────────────────────────────────────────────────┘
│            │                                                            │
│            ▼                                                            │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  Commit Logic     │                                                  │
│  │ (In-order Retirement)│                                                  │
│  └─────┬─────┬───────┘                                                  │
│        │     │                                                          │
│        ▼     ▼                                                          │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  Commit Outputs   │                                                  │
│  │ (To Reg File, CSRs)│                                                  │
│  └───────────────────┘                                                  │
└───────────────────────────────────────────────────────────────────────────┘
```

- **Functionality**:
    - **ROB Entries**: A circular buffer (`rob_r`) that stores information about all in-flight instructions, including their PC, destination register, result, and exception status. Each entry is identified by a unique ROB tag.
    - **Head and Tail Pointers**: `head_ptr_r` points to the oldest instruction in the ROB (the next one to commit), and `tail_ptr_r` points to the next available entry for a new dispatched instruction.
    - **Dispatch Logic**: When a new instruction is dispatched, an entry is allocated at the `tail_ptr_r`, and the instruction's PC and destination register are stored. The `dispatch_rob_tag_o` is provided to the renaming unit and reservation station.
    - **Execution Result Update**: When an instruction completes execution, its result (`execute_result_i`) and exception status (`execute_exception_valid_i`, `execute_exception_cause_i`) are written to its corresponding ROB entry, and the entry is marked as ready (`is_ready`).
    - **Commit Logic**: Instructions are committed from the head of the ROB in program order. An instruction can only commit if it is at the head of the ROB and its `is_ready` flag is set. Upon commitment, its result is written to the architectural register file, and its ROB entry is freed.
    - **Precise Exceptions**: If an instruction at the head of the ROB has an exception, the ROB signals the exception, and all subsequent (younger) instructions in the ROB are flushed, ensuring precise exception handling.
- **Implementation Nuances**:
    - **Circular Buffer Management**: The `head_ptr_r` and `tail_ptr_r` are managed as circular pointers, wrapping around the `ROB_SIZE`.
    - **Entry Count**: `entry_count_r` tracks the number of active entries in the ROB, used to determine `is_full_c` and `is_empty_c`.
    - **Flush Handling**: On a flush signal (`flush_i`), the ROB is reset, clearing all speculative state and pointers, which is crucial for recovering from mispredictions or exceptions.
    - **`rob_entry_t`**: A packed struct defining the contents of each ROB entry.

### 2.4. Register Renaming (`rtl/execution/register_renaming.sv`)
- **Purpose**: Eliminates Write-After-Read (WAR) and Write-After-Write (WAW) hazards by mapping architectural registers to a larger pool of physical registers.
- **Internal Structure and Data Flow**:

```
┌───────────────────────────────────────────────────────────────────────────┐
│                                 Register Renaming                         │
│                                                                           │
│  ┌───────────────────┐     ┌───────────────────┐     ┌───────────────────┐
│  │                   │     │                   │     │                   │
│  │  Decode Inputs    │     │   Map Table       │     │ Physical Register │
│  │ (Arch Reg Addrs)  │     │ (Arch Reg -> ROB Tag) │     │ File (PRF)        │
│  └─────────┬─────────┘     └─────────┬─────────┘     └─────────┬─────────┘
│            │                         │                         │
│            ▼                         ▼                         ▼
│  ┌───────────────────────────────────────────────────────────────────┐
│  │                       Operand Fetch Logic                       │
│  │ (Looks up tags/values from Map Table and PRF)                   │
│  └─────────┬─────────────────────────────────────────────────────────┘
│            │                                                            │
│            ▼                                                            │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  Dispatch Outputs │                                                  │
│  │ (Values or Tags)  │                                                  │
│  └─────┬─────┬───────┘                                                  │
│        │     │                                                          │
│        ▼     ▼                                                          │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  CDB Snooping     │                                                  │
│  │ (Updates PRF)     │                                                  │
│  └───────────────────┘                                                  │
└───────────────────────────────────────────────────────────────────────────┘
```

- **Functionality**:
    - **Map Table**: A key component (`map_table_r`) that stores the mapping from architectural register addresses to their corresponding physical register tags (which are typically ROB tags). It also tracks if a register has a pending write (`busy` bit).
    - **Physical Register File (PRF)**: A larger register file (`prf_r`) that stores the actual data values for all speculative results. It is indexed by the physical register tag (ROB tag).
    - **Operand Fetch**: When an instruction is dispatched, the renaming unit looks up the architectural source register addresses in the Map Table. If a mapping exists and the physical register is ready (i.e., its value has been written back to the PRF), the actual data value is provided. Otherwise, the physical tag (ROB tag) is provided, indicating that the operand is not yet ready.
    - **CDB Snooping**: The PRF continuously monitors the Common Data Bus (CDB). When a result is broadcast on the CDB, the PRF updates the corresponding physical register entry and marks it as ready.
    - **New Mapping Allocation**: When an instruction that writes to a destination register is dispatched, a new physical tag (ROB tag) is allocated for it, and the Map Table is updated to point to this new tag for that architectural register.
    - **Commit Stage Interaction**: When an instruction commits, the renaming unit is informed. If the committing instruction's destination register is still mapped to its ROB tag, that mapping is cleared, indicating that the architectural register file now holds the correct value.
- **Implementation Nuances**:
    - **`map_table_entry_t`**: A packed struct used for entries in the Map Table, containing the ROB tag and a busy bit.
    - **`prf_ready_r`**: A bitmask that tracks which physical register entries in the PRF have valid data.
    - **Prioritized Updates**: The logic for updating the Map Table and PRF is carefully prioritized to handle simultaneous dispatch, result broadcast, and commit operations correctly.
    - **Flush Handling**: On a flush (e.g., due to an exception or misprediction), the speculative state in the Map Table and PRF is cleared.

### 2.5. Multiple Execution Units (`rtl/execution/multiple_execution_units.sv`)
- **Purpose**: Acts as a central dispatcher and arbiter for various functional units (ALU, Multiplier, Divider, etc.). It takes issued instructions from the Reservation Station, routes them to an available functional unit of the correct type, and arbitrates for the result bus (CDB) to write back results.
- **Internal Structure and Data Flow**:

```
┌───────────────────────────────────────────────────────────────────────────┐
│                           Multiple Execution Units                        │
│                                                                           │
│  ┌───────────────────┐     ┌───────────────────┐     ┌───────────────────┐
│  │                   │     │                   │     │                   │
│  │  Issued Instruction │     │  Instruction      │     │  Functional Unit  │
│  │  (from RS)        │     │  Decoder          │     │  Pool (ALU, MUL, DIV) │
│  └─────────┬─────────┘     └─────────┬─────────┘     └─────────┬─────────┘
│            │                         │                         │
│            ▼                         ▼                         ▼
│  ┌───────────────────────────────────────────────────────────────────┐
│  │                       Dispatcher Logic                            │
│  │ (Routes instruction to available FU based on type)                │
│  └─────────┬─────────────────────────────────────────────────────────┘
│            │                                                            │
│            ▼                                                            │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  Result Arbiter   │                                                  │
│  │ (Selects one result)│                                                  │
│  └─────┬─────┬───────┘                                                  │
│        │     │                                                          │
│        ▼     ▼                                                          │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  Result Bus (CDB) │                                                  │
│  │                   │                                                  │
│  └───────────────────┘                                                  │
└───────────────────────────────────────────────────────────────────────────┘
```

- **Functionality**:
    - **Instruction Decoder**: A combinational block that determines the required functional unit type (ALU, Multiplier, Divider) from the issued instruction's opcode and function fields.
    - **Dispatcher**: Routes the issued instruction (operands, ROB tag) to a free functional unit of the determined type. It manages the `issue_ready_o` signal to the Reservation Station, indicating readiness to accept new instructions based on the availability of functional units.
    - **Functional Unit Pool**: Instantiates multiple instances of `alu.sv`, `mult_unit.sv`, and `div_unit.sv` (parameterized by `NUM_ALU_UNITS`, `NUM_MULT_UNITS`, `NUM_DIV_UNITS`). Each unit performs its specific operation and signals `done_o` upon completion.
    - **Result Arbiter**: A fixed-priority arbiter that selects one valid result from the completed functional units to drive the Common Data Bus (CDB). It ensures that only one result is broadcast at a time, along with its ROB tag and any exception information.
- **Implementation Nuances**:
    - **Pipelined ROB Tag**: The ROB tag of an issued instruction is pipelined through the functional units to ensure it aligns with the result when it becomes valid.
    - **Multi-cycle Unit Handling**: The `busy_o` signal from multi-cycle units (Multiplier, Divider) is used to track their availability, preventing new instructions from being dispatched to them until they are free.
    - **Exception Propagation**: Functional units can signal exceptions (e.g., division by zero), which are then propagated through the result arbiter to the CDB.

## 3. OoO Execution Flow

1.  **Fetch & Decode**: Instructions are fetched and decoded in program order.
2.  **Dispatch**: Decoded instructions are dispatched to available Reservation Stations. Register renaming occurs here, and a new entry is allocated in the ROB.
3.  **Issue**: Instructions in Reservation Stations monitor the CDB. When all operands are ready and a functional unit is available, the instruction is issued for execution.
4.  **Execute**: The functional unit executes the instruction. The result is written to the ROB entry and broadcast on the CDB.
5.  **Writeback**: Results from the CDB are written to the physical register file and updated in the Reservation Stations.
6.  **Commit/Retire**: Instructions are committed from the ROB in program order. Once an instruction commits, its result is written to the architectural register file, and its ROB entry is freed.

## 4. Hazard Handling in OoO

OoO execution inherently handles WAR and WAW hazards through register renaming. RAW hazards are handled by waiting for operands in the Reservation Stations and using the CDB for fast result propagation.

## 5. Integration with Pipeline

The OoO engine sits between the Decode and Writeback stages of the traditional pipeline. Instructions enter the OoO engine after Decode and exit to the Writeback stage after commitment.

## 6. Future Enhancements
- **Load/Store Queue**: For handling memory dependencies and speculative loads/stores.
- **Power Management**: Techniques to reduce power consumption in OoO units.
- **Floating Point/Vector/ML Units**: Integration of FPU, VPU, and MLIU into the `multiple_execution_units` framework for OoO execution.

## 7. Current Implementation Status
The Out-of-Order execution engine (`ooo_engine.sv`) has been implemented, integrating the Reservation Station (`reservation_station.sv`), Reorder Buffer (`reorder_buffer.sv`), Register Renaming (`register_renaming.sv`), and Multiple Execution Units (`multiple_execution_units.sv`). This implementation includes:
- Precise exception handling.
- Integration with the existing branch prediction unit for speculative execution.
