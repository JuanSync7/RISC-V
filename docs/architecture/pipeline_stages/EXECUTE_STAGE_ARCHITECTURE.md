# Execute Stage (E) Architecture

## 1. Overview

The Execute Stage (E) is the third stage of the RISC-V pipeline. It is responsible for performing the actual computation of instructions, including arithmetic and logical operations, multiplication, division, and specialized Data Processing Unit (DPU) operations. It also handles data forwarding, evaluates branch conditions, calculates jump targets, and detects various exceptions.

## 2. Key Components and Data Flow

### 2.1. Conceptual Block Diagram

```
┌───────────────────────────────────────────────────────────────────────────┐
│                                 Execute Stage (E)                         │
│                                                                           │
│  ┌───────────────────┐     ┌───────────────────┐     ┌───────────────────┐
│  │                   │     │                   │     │                   │
│  │  ID/EX Register   │     │ Forwarding Logic  │     │   ALU / Multi-    │
│  │ (Input from Decode)│     │                   │     │   cycle Units     │
│  └─────────┬─────────┘     └─────────┬─────────┘     └─────────┬─────────┘
│            │                         │                         │
│            ▼                         ▼                         ▼
│  ┌───────────────────────────────────────────────────────────────────┐
│  │                       Branch Evaluation Logic                     │
│  │ (Conditional Branch, Jump Target Calculation)                     │
│  └─────────┬─────────────────────────────────────────────────────────┘
│            │                                                            │
│            ▼                                                            │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  PC Redirect Logic│                                                  │
│  │                   │                                                  │
│  └─────┬─────┬───────┘                                                  │
│        │     │                                                          │
│        ▼     ▼                                                          │
│  ┌───────────────────┐                                                  │
│  │                   │                                                  │
│  │  EX/MEM Register  │                                                  │
│  │ (Output to Memory)│                                                  │
│  └───────────────────┘                                                  │
└───────────────────────────────────────────────────────────────────────────┘
```

### 2.2. Component Descriptions

-   **ID/EX Register**: This pipeline register (`id_ex_reg_i`) receives decoded instruction information, operand data, and control signals from the Decode stage.
-   **Forwarding Logic**: Selects the correct operand values (`fwd_operand_a`, `fwd_operand_b`) for the ALU and other functional units. It resolves Read-After-Write (RAW) data hazards by forwarding results from later pipeline stages (Memory, Writeback) if they are available sooner than from the Register File.
-   **ALU (`alu` instance)**: Performs all single-cycle arithmetic and logical operations.
-   **Multi-cycle Units**: Includes instances of `mult_unit` (Multiplier), `div_unit` (Divider), `fpu_unit` (Floating Point Unit), `vpu_unit` (Vector Processing Unit), and `ml_inference_unit` (Machine Learning Inference Unit). These units handle complex, multi-cycle operations.
-   **Branch Evaluation Logic**: Determines if a conditional branch is taken based on ALU flags (e.g., zero flag) and calculates the target address for branches and jumps.
-   **PC Redirect Logic**: Generates the `pc_redirect_o` and `pc_redirect_target_o` signals to redirect the Program Counter in the Fetch stage for taken branches, jumps, and exceptions.
-   **Exception Detection Logic**: Identifies various exceptions originating in the Execute stage (e.g., illegal instruction, division by zero, overflow, ECALL, EBREAK).
-   **EX/MEM Register**: This pipeline register (`ex_mem_reg_o`) latches the results and control signals, passing them to the Memory stage.

## 3. Detailed Logic Flow

### 3.1. Operand Selection and Forwarding

The `forward_a_sel_i` and `forward_b_sel_i` signals (from the Hazard Unit) control multiplexers that select the source of `fwd_operand_a` and `fwd_operand_b`:
-   `FWD_SEL_REG` (00): Operand comes from the Register File (via ID/EX register).
-   `FWD_SEL_MEM` (01): Operand is forwarded from the Memory stage (`ex_mem_reg_m_i.alu_result`).
-   `FWD_SEL_WB` (10): Operand is forwarded from the Writeback stage (`wb_data_w_i`).

ALU inputs (`alu_operand_a`, `alu_operand_b`) are then selected from these forwarded operands or the PC/immediate based on `alu_src_a_sel` and `alu_src_b_sel` from the Decode stage.

### 3.2. Multi-cycle Operation Handling

-   **Stall Generation**: The `exec_stall_req_o` signal is asserted if a multi-cycle operation (multiplication, division, or DPU operation) is initiated and its `done_o` signal is not yet asserted. This stalls the upstream pipeline stages until the operation completes.
-   **Result Selection**: The `final_result` is multiplexed from the outputs of the ALU, multiplier, divider, or DPU units based on the control signals (`mult_en`, `div_en`, `dpu_en`, `dpu_unit_sel`).

### 3.3. Branch Evaluation and PC Redirect

-   **Branch Taken Logic**: For conditional branches, `branch_taken` is determined by comparing `fwd_operand_a` and `fwd_operand_b` using the ALU and checking the `alu_zero_flag` or `alu_result[0]` based on the `funct3` field.
-   **PC Redirect**: The `pc_redirect_o` signal is asserted if `branch_taken` is true (for conditional branches) or if the instruction is an unconditional jump (JAL, JALR). The `pc_redirect_target_o` is calculated based on the PC and immediate for jumps, or the ALU result for JALR.

### 3.4. Exception Detection

The Execute stage detects and prioritizes several exceptions:
-   **Illegal Instruction**: If `id_ex_reg_i.ctrl.illegal_instr` is set by the Decode stage, or if an unsupported DPU is enabled.
-   **Division by Zero**: Detected if `div_en` is asserted and the divisor (`fwd_operand_b`) is zero.
-   **Arithmetic Overflow**: Detected by the `alu_overflow_flag` for ADD/SUB operations.
-   **ECALL/EBREAK**: Detected by specific immediate values in SYSTEM instructions.

Detected exceptions are latched into `exception_detected` and propagated via `exception_o` to the central exception handler.

### 3.5. Branch Prediction Update

The `bp_update_o` signal provides feedback to the Branch Prediction Unit (BPU) in the Fetch stage. It includes the PC of the branch, whether it was actually taken (`branch_taken`), and the actual target address. This information is crucial for training dynamic branch predictors.

### 3.6. Pipeline Register (EX/MEM) Update

The `ex_mem_reg_q` (EX/MEM pipeline register) is updated on the positive clock edge:
-   **Reset**: On reset, it's initialized with NOP-like values.
-   **Stall**: If `stall_m_i` is asserted, the register holds its current value.
-   **Flush**: If `flush_e_i` is asserted, the register is loaded with NOP-like values, clearing the pipeline.
-   **Normal Operation**: Otherwise, it latches the `final_result`, `store_data` (for memory writes), `rd_addr`, `alu_overflow`, and `exception_detected` information, along with the control signals (`id_ex_reg_i.ctrl`).

## 4. Implementation Nuances

-   **Multi-cycle Unit Integration**: The design effectively integrates multi-cycle units by using stall signals to manage pipeline flow, ensuring correctness without complex bypass networks for these units.
-   **Forwarding Paths**: The forwarding logic is critical for performance, reducing stalls due to data dependencies.
-   **Exception Prioritization**: Exceptions are detected and prioritized within the stage before being passed to the central handler.
-   **Extensibility**: The DPU integration (`fpu_unit`, `vpu_unit`, `ml_inference_unit`) demonstrates how specialized functional units can be added and controlled by the Decode and Execute stages.

## 5. Interfaces

-   **`clk_i`, `rst_ni`**: System clock and reset.
-   **`stall_m_i`, `flush_e_i`**: Control signals from the Hazard Unit for pipeline control.
-   **`forward_a_sel_i`, `forward_b_sel_i`**: Forwarding select signals from the Hazard Unit.
-   **`id_ex_reg_i`**: Input pipeline register from the Decode stage.
-   **`ex_mem_reg_m_i`, `wb_data_w_i`**: Inputs for forwarding data from Memory and Writeback stages.
-   **`pc_redirect_o`, `pc_redirect_target_o`**: Outputs for PC redirection to the Fetch stage.
-   **`exec_stall_req_o`**: Output to the Hazard Unit to request a stall for multi-cycle operations.
-   **`overflow_o`**: Output for arithmetic overflow detection.
-   **`bp_update_o`**: Output for branch prediction updates to the Fetch stage.
-   **`exception_o`**: Output for detected exceptions.
-   **`ex_mem_reg_o`**: Output pipeline register to the Memory stage.
