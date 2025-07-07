# RISC-V Multiple Execution Units Architecture

**Location:** `docs/architecture/`
**Purpose:** Detailed architectural documentation of the `multiple_execution_units.sv` module.
**Module:** `rtl/core/execution/multiple_execution_units.sv`

---

## Overview

The `multiple_execution_units.sv` module acts as a central dispatcher and arbiter for various functional units (FUs) within the RISC-V core's out-of-order execution engine. It receives instructions from the Reservation Station, decodes their operation type, dispatches them to an available FU of the correct type (ALU, Multiplier, Divider), and arbitrates for the Common Data Bus (CDB) to broadcast results back to other pipeline stages and the Physical Register File.

---

## Module Parameters

| Parameter Name    | Type    | Description                                                              | Default Value |
|-------------------|---------|--------------------------------------------------------------------------|---------------|
| `DATA_WIDTH`      | `integer` | Width of the data path and register values (e.g., 32 for RV32).          | `XLEN`        |
| `ROB_ADDR_WIDTH`  | `integer` | Width of the Reorder Buffer (ROB) tag, used for tracking instructions.   | `$clog2(DEFAULT_ROB_SIZE)` |
| `NUM_ALU_UNITS`   | `integer` | Number of parallel Arithmetic Logic Units.                               | `DEFAULT_NUM_ALU_UNITS` |
| `NUM_MULT_UNITS`  | `integer` | Number of parallel Multiplier Units.                                     | `DEFAULT_NUM_MULT_UNITS` |
| `NUM_DIV_UNITS`   | `integer` | Number of parallel Division Units.                                       | `DEFAULT_NUM_DIV_UNITS` |

---

## Ports

| Port Name                 | Direction | Type                               | Description                                                              |
|---------------------------|-----------|------------------------------------|--------------------------------------------------------------------------|
| `clk_i`                   | Input     | `logic`                            | System clock input.                                                      |
| `rst_ni`                  | Input     | `logic`                            | Asynchronous reset, active low.                                          |
| `issue_ready_o`           | Output    | `logic`                            | Indicates if the module is ready to accept a new instruction from the RS.|
| `issue_valid_i`           | Input     | `logic`                            | A valid instruction is being issued from the Reservation Station.        |
| `issue_opcode_i`          | Input     | `riscv_instr_t`                    | Opcode of the issued instruction, used for FU selection.                 |
| `issue_v_rs1_i`           | Input     | `logic [DATA_WIDTH-1:0]`           | Value of operand 1 for the issued instruction.                           |
| `issue_v_rs2_i`           | Input     | `logic [DATA_WIDTH-1:0]`           | Value of operand 2 for the issued instruction.                           |
| `issue_rob_tag_i`         | Input     | `logic [ROB_ADDR_WIDTH-1:0]`       | ROB tag associated with the issued instruction.                          |
| `result_valid_o`          | Output    | `logic`                            | A valid result is available on the Common Data Bus (CDB).                |
| `result_rob_tag_o`        | Output    | `logic [ROB_ADDR_WIDTH-1:0]`       | ROB tag of the instruction whose result is on the CDB.                   |
| `result_data_o`           | Output    | `logic [DATA_WIDTH-1:0]`           | Result data from the completed instruction.                              |
| `result_exception_valid_o`| Output    | `logic`                            | Indicates if the completed instruction caused an exception.              |
| `result_exception_cause_o`| Output    | `logic [31:0]`                     | Cause of the exception, if `result_exception_valid_o` is high.           |

---

## Internal Structure and Logic

The `multiple_execution_units` module comprises three main conceptual blocks:

1.  **Instruction Decoder**: Determines the type of functional unit required for an incoming instruction based on its opcode.
2.  **Functional Unit Instantiations**: Generates and connects multiple instances of ALU, Multiplier, and Divider units.
3.  **Dispatcher & `issue_ready_o` Logic**: Manages the allocation of instructions to available functional units and signals readiness to the Reservation Station.
4.  **Result Arbiter**: Selects one completed result from the functional units to broadcast onto the Common Data Bus (CDB).

### Instruction Decoder

This combinational logic block analyzes the `issue_opcode_i` to determine if the instruction is an ALU operation, a multiplication, or a division. It sets internal flags (`is_alu_op_c`, `is_mult_op_c`, `is_div_op_c`) accordingly.

```systemverilog
    always_comb begin : proc_instr_decoder
        is_alu_op_c  = 1'b0;
        is_mult_op_c = 1'b0;
        is_div_op_c  = 1'b0;

        case (issue_opcode_i.op)
            OP_IMM, OP: begin
                // M-extension standard: funct7 = 0000001 for MUL/DIV/REM
                if (issue_opcode_i.funct7 == 7'b0000001) begin
                    case (issue_opcode_i.funct3)
                        // All MULT opcodes
                        3'b000, 3'b001, 3'b010, 3'b011: is_mult_op_c = 1'b1;
                        // All DIV/REM opcodes
                        3'b100, 3'b101, 3'b110, 3'b111: is_div_op_c = 1'b1;
                        default: is_alu_op_c = 1'b1; // Should not happen with valid instructions
                    endcase
                end else begin
                    is_alu_op_c = 1'b1;
                end
            end
            default:    is_alu_op_c = 1'b1; // Default to ALU for branches, loads, stores, etc.
        endcase
    end
```

### Functional Unit Instantiations

This module instantiates multiple copies of `alu`, `mult_unit`, and `div_unit` based on the `NUM_ALU_UNITS`, `NUM_MULT_UNITS`, and `NUM_DIV_UNITS` parameters. Each unit has its own `start` signal, which is asserted when an instruction of its type is ready to be dispatched and the unit is not busy. The `ROB` tag is pipelined with the instruction to ensure correct result association.

```systemverilog
    // --- ALUs ---
    generate
        for (genvar i = 0; i < NUM_ALU_UNITS; i++) begin : gen_alu_units
            // ... ALU instantiation and wiring ...
        end
    endgenerate

    // --- Multipliers ---
    generate
        for (genvar i = 0; i < NUM_MULT_UNITS; i++) begin : gen_mult_units
            // ... Multiplier instantiation and wiring ...
        end
    endgenerate

    // --- Division Units ---
    generate
        for (genvar i = 0; i < NUM_DIV_UNITS; i++) begin : gen_div_units
            // ... Divider instantiation and wiring ...
        end
    endgenerate
```

### Dispatcher & `issue_ready_o` Logic

This section determines if the `multiple_execution_units` module is ready to accept a new instruction. It checks if there is an available (not busy) functional unit of the type required by the incoming instruction. The `issue_ready_o` signal is asserted if at least one suitable unit is free.

```systemverilog
    assign alu_units_full_c  = &fu_busy_c[TOTAL_ALU_UNITS-1:0];
    assign mult_units_full_c = &fu_busy_c[TOTAL_MULT_UNITS-1:TOTAL_ALU_UNITS];
    assign div_units_full_c  = &fu_busy_c[TOTAL_UNITS-1:TOTAL_MULT_UNITS];

    assign issue_ready_o = (is_alu_op_c  && !alu_units_full_c) ||
                           (is_mult_op_c && !mult_units_full_c) ||
                           (is_div_op_c  && !div_units_full_c);
```

### Result Arbiter

This combinational block arbitrates among the completed functional units to select one result to be broadcast on the Common Data Bus (CDB). It uses a fixed-priority scheme, iterating through the functional units and selecting the first one with a valid result. This result, along with its ROB tag and any exception information, is then driven to the `result_valid_o`, `result_rob_tag_o`, `result_data_o`, `result_exception_valid_o`, and `result_exception_cause_o` outputs.

```systemverilog
    always_comb begin : proc_result_arbiter
        result_valid_o           = 1'b0;
        result_rob_tag_o         = '0;
        result_data_o            = '0;
        result_exception_valid_o = 1'b0;
        result_exception_cause_o = '0;

        for (int i = 0; i < TOTAL_UNITS; i++) begin
            if (fu_result_valid_c[i]) begin
                result_valid_o           = 1'b1;
                result_rob_tag_o         = fu_result_rob_tag_c[i];
                result_data_o            = fu_result_data_c[i];
                result_exception_valid_o = fu_result_ex_valid_c[i];
                result_exception_cause_o = fu_result_ex_cause_c[i];
                break; // This creates the fixed priority
            end
        end
    end
```

---

**Document Version:** 1.0
**Last Updated:** 2025-07-06
**Maintainer:** RISC-V RTL Team
**Status:** Draft