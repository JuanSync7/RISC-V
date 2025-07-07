# Decode Stage (D) Architecture

## 1. Overview

The Decode Stage (D) is the second stage of the RISC-V pipeline. Its primary responsibilities include interpreting the fetched instruction, generating all necessary control signals for subsequent pipeline stages, extracting and sign-extending immediate values, and reading operand values from the Register File.

## 2. Key Components and Data Flow

### 2.1. Conceptual Block Diagram

```
┌───────────────────────────────────────────────────────────────────────────┐
│                                 Decode Stage (D)                          │
│                                                                           │
│  ┌───────────────────┐     ┌───────────────────┐     ┌───────────────────┐
│  │                   │     │                   │     │                   │
│  │  IF/ID Register   │     │ Instruction Decoder │     │  Immediate Generator  │
│  │ (Input from Fetch)│     │                   │     │                   │
│  └─────────┬─────────┘     └─────────┬─────────┘     └─────────┬─────────┘
│            │                         │                         │
│            ▼                         ▼                         ▼
│  ┌───────────────────────────────────────────────────────────────────┐
│  │                       Control Signal Generation                 │
│  │ (ALU Ops, Mem Control, Reg Write, Branch, DPU, CSR)             │
│  └─────────┬─────────────────────────────────────────────────────────┘
│            │                                                            │
│            ▼                                                            │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  Register File    │                                                  │
│  │  Read Ports       │                                                  │
│  └─────┬─────┬───────┘                                                  │
│        │     │                                                          │
│        ▼     ▼                                                          │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  ID/EX Register   │                                                  │
│  │ (Output to Execute)│                                                  │
│  └───────────────────┘                                                  │
└───────────────────────────────────────────────────────────────────────────┘
```

### 2.2. Component Descriptions

-   **IF/ID Register**: This pipeline register (`if_id_reg_i`) receives the fetched instruction and its Program Counter (PC) from the Fetch stage.
-   **Instruction Decoder**: This combinational logic is the core of the Decode stage. It parses the instruction fields (opcode, funct3, funct7, rs1, rs2, rd) and generates all necessary control signals (`ctrl_d`) for the Execute, Memory, and Writeback stages.
-   **Immediate Generator**: This combinational logic extracts and sign-extends the immediate value (`immediate_d`) from the instruction based on its type (I-type, S-type, B-type, U-type, J-type).
-   **Register File Read Ports**: The Decode stage provides the addresses of the source registers (`rs1_addr_o`, `rs2_addr_o`) to the Register File and receives the corresponding data (`rs1_data_i`, `rs2_data_i`).
-   **ID/EX Register**: This pipeline register (`id_ex_reg_o`) latches all the decoded information (PC, operand data, immediate, control signals, destination register address) and passes it to the Execute stage.

## 3. Detailed Logic Flow

### 3.1. Instruction Decoding and Control Signal Generation

The main instruction decoder is implemented using a large `case` statement on the instruction's `opcode`. Within each opcode block, further `case` statements on `funct3` and `funct7` fields differentiate specific instructions.

-   **Default Control Signals**: All control signals (`ctrl_d`) are assigned default (NOP) values at the beginning of the `always_comb` block to prevent unintended latches.
-   **Instruction Validity**: Decoding only proceeds if `if_id_reg_i.valid` is asserted, ensuring that only valid instructions are processed.
-   **Control Signal Fields**: The `ctrl_signals_t` struct contains various fields for:
    -   ALU operation (`alu_op`, `alu_src_a_sel`, `alu_src_b_sel`)
    -   Memory access (`mem_read_en`, `mem_write_en`)
    -   Register write-back (`reg_write_en`, `wb_mux_sel`)
    -   Branch indication (`is_branch`)
    -   M-extension operations (`mult_en`, `div_en`)
    -   CSR operations (`csr_cmd_en`)
    -   DPU operations (`dpu_en`, `dpu_unit_sel`, `dpu_op_sel`)
    -   Illegal instruction detection (`illegal_instr`)

### 3.2. Immediate Generation

The `immediate_d` is generated based on the instruction format. The logic correctly extracts and sign-extends the immediate bits for each instruction type (I, S, B, U, J).

### 3.3. Register File Access

The `rs1_addr` and `rs2_addr` fields from the instruction are directly used as addresses for the Register File read ports. The data read from the Register File (`rs1_data_i`, `rs2_data_i`) is then latched into the ID/EX pipeline register.

### 3.4. Pipeline Register (ID/EX) Update

The `id_ex_reg_q` (ID/EX pipeline register) is updated on the positive clock edge:
-   **Reset**: On reset, it's initialized with NOP-like values.
-   **Stall**: If `stall_e_i` is asserted, the register holds its current value.
-   **Flush**: If `flush_d_i` is asserted, the register is loaded with NOP-like values, injecting a bubble.
-   **Normal Operation**: Otherwise, it latches the PC, operand data, immediate, control signals, and destination register address.
-   **Source Register Addresses**: The `rs1_addr` and `rs2_addr` are also latched into the ID/EX register for use by the Hazard Unit in the Execute stage.
-   **DPU Operands**: Operands for DPUs (FPU, VPU, MLIU) are also latched into the ID/EX register.

## 4. Implementation Nuances

-   **Combinational Logic**: The Decode stage is primarily combinational logic, ensuring fast instruction decoding. Pipelining is handled by the IF/ID and ID/EX registers.
-   **Illegal Instruction Detection**: The `illegal_instr` signal is asserted for unrecognized opcodes or invalid function field combinations, triggering an exception.
-   **RVC Instruction Support (Future)**: The current decoder assumes 32-bit instructions. For RVC support, the decoding logic will need to be extended to handle 16-bit instructions and their unique immediate formats.
-   **DPU Integration**: The decoder includes logic to enable and select specific Data Processing Units (FPU, VPU, MLIU) based on custom opcodes, demonstrating extensibility.

## 5. Interfaces

-   **`clk_i`, `rst_ni`**: System clock and reset.
-   **`stall_e_i`, `flush_d_i`**: Control signals from the Hazard Unit for pipeline control.
-   **`if_id_reg_i`**: Input pipeline register from the Fetch stage.
-   **Register File Interface**: `rs1_addr_o`, `rs2_addr_o` (outputs to RegFile), `rs1_data_i`, `rs2_data_i` (inputs from RegFile).
-   **`id_ex_reg_o`**: Output pipeline register to the Execute stage.
