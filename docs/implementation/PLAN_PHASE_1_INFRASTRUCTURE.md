# Detailed Plan: Phase 1 - Foundational Infrastructure

**Version:** 1.0
**Status:** Not Started

## 1. Objective

This phase establishes the fundamental building blocks of the entire RISC-V project. The primary goal is to create a solid, well-documented, and rule-compliant foundation of packages, interfaces, and module skeletons. Completing this phase is a prerequisite for any RTL logic development.

## 2. Task Breakdown

### Task 1.1: Core Package Creation

*   **Status:** `Not Started`
*   **Objective:** Create the `riscv_config_pkg` and `riscv_types_pkg` to centralize configuration and type definitions.
*   **Rules Compliance:** Adheres to `systemverilog-package-distinction.mdc` and `risc-v-package-hierarchy.mdc`.

#### Sub-Task 1.1.1: Create `riscv_config_pkg.sv`

*   **File Location:** `rtl/config/riscv_config_pkg.sv`
*   **Content:**
    ```systemverilog
    //=============================================================================
    // Company: Sondrel Ltd
    // Project Name: RISC-V Core
    //
    // File: riscv_config_pkg.sv
    //
    // MODULE_NAME: riscv_config_pkg
    // AUTHOR: DesignAI (designai@sondrel.com)
    // VERSION: 1.0.0
    // DATE: 2025-07-07
    // DESCRIPTION: Contains all user-configurable parameters for the RISC-V system.
    //              This package is intended to be modified by the system integrator.
    // MODULE_TYPE: Package
    //=============================================================================

    package riscv_config_pkg;

        // -- Core Architecture --
        parameter int CONFIG_XLEN = 32; // Data width (32 or 64)
        parameter int CONFIG_NUM_CORES = 4; // Number of cores in a multi-core system
        parameter logic [CONFIG_XLEN-1:0] CONFIG_RESET_VECTOR = 32'h80000000; // Default reset vector

        // -- Execution Mode --
        parameter string CONFIG_EXECUTION_MODE = "IN_ORDER"; // "IN_ORDER" or "OUT_OF_ORDER"

        // -- Optional Features --
        parameter bit CONFIG_ENABLE_MMU = 1'b1;
        parameter bit CONFIG_ENABLE_FPU = 1'b1;
        parameter bit CONFIG_ENABLE_VPU = 1'b0; // Vector Processing Unit
        parameter bit CONFIG_ENABLE_ML_INFERENCE = 1'b0; // ML Inference Unit
        parameter bit CONFIG_ENABLE_BUS_WATCHDOG = 1'b1;
        parameter bit CONFIG_ENABLE_PMU = 1'b1;

        // -- Branch Predictor --
        parameter string CONFIG_BRANCH_PREDICTOR_TYPE = "GSHARE"; // "STATIC", "GSHARE", "TOURNAMENT"
        parameter int CONFIG_BTB_ENTRIES = 512;
        parameter int CONFIG_BHT_ENTRIES = 1024;

        // -- Caches --
        parameter int CONFIG_L1_CACHE_SIZE = 32 * 1024; // 32KB
        parameter int CONFIG_L2_CACHE_SIZE = 256 * 1024; // 256KB
        parameter int CONFIG_L3_CACHE_SIZE = 2 * 1024 * 1024; // 2MB

    endpackage
    ```

#### Sub-Task 1.1.2: Create `riscv_types_pkg.sv`

*   **File Location:** `rtl/pkg/riscv_types_pkg.sv`
*   **Content:**
    ```systemverilog
    //=============================================================================
    // Company: Sondrel Ltd
    // Project Name: RISC-V Core
    //
    // File: riscv_types_pkg.sv
    //
    // MODULE_NAME: riscv_types_pkg
    // AUTHOR: DesignAI (designai@sondrel.com)
    // VERSION: 1.0.0
    // DATE: 2025-07-07
    // DESCRIPTION: Contains fixed, internal type definitions for the RISC-V core.
    //              This package should not be modified by the user.
    // MODULE_TYPE: Package
    //=============================================================================

    package riscv_types_pkg;
        import riscv_config_pkg::*;

        // -- Basic Types --
        typedef logic [CONFIG_XLEN-1:0] word_t;
        typedef logic [4:0]             reg_addr_t;
        typedef logic [31:0]            inst_t;
        typedef logic [CONFIG_XLEN-1:0] addr_t;

        // -- ALU Operations --
        typedef enum logic [3:0] {
            ALU_ADD, ALU_SUB, ALU_XOR, ALU_OR, ALU_AND,
            ALU_SLL, ALU_SRL, ALU_SRA, ALU_SLT, ALU_SLTU
        } alu_op_e;

        // -- Pipeline Stage Structs --
        typedef struct packed {
            addr_t   pc;
            inst_t   inst;
            logic    valid;
        } fetch_decode_t;

        typedef struct packed {
            addr_t      pc;
            word_t      operand_a;
            word_t      operand_b;
            reg_addr_t  rd_addr;
            alu_op_e    alu_op;
            logic       is_branch;
            logic       is_jump;
            logic       is_mem_read;
            logic       is_mem_write;
            logic       valid;
        } decode_execute_t;

        // ... other pipeline structs to be defined as needed ...

    endpackage
    ```

#### Sub-Task 1.1.3: Documentation

*   **File Location:** `docs/architecture/KEY_PACKAGES_AND_TYPES.md`
*   **Content:** A markdown file explaining the purpose of the `config` and `pkg` directories, the distinction between them, and a summary of the key types and parameters defined in this phase.

#### Sub-Task 1.1.4: Verification

*   **Objective:** Ensure the created packages are syntactically correct and can be compiled in the correct dependency order.
*   **Procedure:** Create a temporary script (`/tmp/compile_pkgs.sh`) that uses a SystemVerilog compiler (like VCS or ModelSim) to compile `riscv_config_pkg.sv` followed by `riscv_types_pkg.sv`. The script should report success if compilation is error-free.

---

### Task 1.2: Core Interface Definition

*   **Status:** `Not Started`
*   **Objective:** Define the primary SystemVerilog interfaces for memory and inter-core communication.
*   **Rules Compliance:** Adheres to `interface-first-rtl-design.mdc`.

#### Sub-Task 1.2.1: Create `memory_req_rsp_if.sv`

*   **File Location:** `rtl/interfaces/memory_req_rsp_if.sv`
*   **Content:**
    ```systemverilog
    // ... (Standard Header) ...
    interface memory_req_rsp_if(input logic clk, input logic rst_n);
        import riscv_types_pkg::*;

        logic        req_valid;
        logic        req_ready;
        addr_t       req_addr;
        logic        req_write;
        word_t       req_wdata;
        logic [CONFIG_XLEN/8-1:0] req_wstrb;

        logic        rsp_valid;
        word_t       rsp_rdata;

        modport master (
            output req_valid, req_addr, req_write, req_wdata, req_wstrb,
            input  req_ready, rsp_valid, rsp_rdata, clk, rst_n
        );

        modport slave (
            input  req_valid, req_addr, req_write, req_wdata, req_wstrb,
            output req_ready, rsp_valid, rsp_rdata,
            input clk, rst_n
        );
    endinterface
    ```

*   **And so on for the other interfaces...**

---

This is the level of detail I will apply to all phases and tasks. I will now proceed to create the remaining detailed plan files.
