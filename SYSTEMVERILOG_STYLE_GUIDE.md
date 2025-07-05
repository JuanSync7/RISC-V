# SystemVerilog RTL Coding and Formatting Style Guide

## Overview
This document defines the SystemVerilog coding and formatting style for RTL design. Adherence to these guidelines is mandatory to ensure code consistency, readability, maintainability, and to facilitate collaboration, synthesis, and verification. This guide complements the IEEE 1800-2017 SystemVerilog standard. For language semantics and syntax, refer to IEEE 1800-2017.

---

## 1. General Formatting

### 1.1. Character Encoding
- UTF-8

### 1.2. Line Length
- Maximum 120 characters. Break longer lines for readability.

### 1.3. Indentation
- 4 spaces per indentation level. Do NOT use tabs.

### 1.4. `timescale
- `` `timescale 1ns/1ps `` must be declared at the top of every SystemVerilog file (`.sv`, `.svh`).

### 1.5. `default_nettype
- `` `default_nettype none `` must be used at the top of each RTL file after `timescale` to prevent implicit wire declarations.

### 1.6. Comments
- `//` for single-line comments.
- `/* ... */` for multi-line block comments (use sparingly in RTL, prefer //).
- Use meaningful comments to explain complex logic, design trade-offs, or non-obvious code sections.
- **Standard Tags**:
  - `// TODO:` Item needing completion.
  - `// FIXME:` Item that is broken and needs fixing.
  - `// NOTE:` Important information or clarification.
  - `// INFO:` General information.
  - `// WARNING:` Potential issue or caution.
  - `// REVIEW:` Code section that needs review.

### 1.7. Preprocessor Directives for Simulation/Synthesis
- Clearly delineate code sections for simulation-only or synthesis-only using standard preprocessor directives:
  ```systemverilog
  `ifdef SIMULATION
    // Simulation-only code (e.g., display statements, specific checks)
  `endif

  `ifdef SYNTHESIS
    // Synthesis-only code (rare, usually for tool-specific attributes)
  `else
    // Code for non-synthesis tools or alternative implementation if SYNTHESIS is not defined
  `endif

  // Alternatively, for code to be excluded from synthesis (prefer the `ifdef method):
  // synthesis translate_off
  ...
  // synthesis translate_on
  ```

---

## 2. Naming Conventions

### 2.1. General
- Use descriptive names. Avoid single-letter names except for loop variables (i, j, k).
- Use snake_case for signals, variables, and most identifiers unless specified.
- Use snake_case for module names, interface names, package names, class names, and typedefs.
- Use UPPER_CASE for parameters, localparams, and macros.

### 2.2. File Naming
- **RTL Modules**: `module_name.sv` (e.g., `data_processor.sv`)
- **Testbenches**: `ModuleName_tb.sv` (e.g., `data_processor_tb.sv`, `fpu_tb.sv`, `vpu_tb.sv`, `mliu_tb.sv`)
- **Packages**: `feature_name_pkg.sv` (e.g., `axi_utils_pkg.sv`)
- **Interfaces**: `purpose_name_if.sv` (e.g., `axi_stream_if.sv`)
- **Include Files**: `header_name_hdr.svh` (e.g., `defines_hdr.svh`)
- **Constraints**: `module_name.sdc` (e.g., `data_processor.sdc`)

### 2.3. Module and Interface Names
- snake_case (e.g., `my_module`, `standard_bus_if`).

### 2.4. Signal Naming
- **Suffixes**:
  - `_i`: input port
  - `_o`: output port
  - `_io`: inout port
  - `_r`: registered signal (output of a flip-flop)
  - `_ns`: next-state signal for a registered signal (combinational)
  - `_c` or `_comb`: combinational logic signal (if clarity needed beyond _ns)
  - `_w`: wire (explicitly, if needed for clarity, often implicit)
  - `_en`: enable signal
  - `_busy`: busy status signal
  - `_valid`: valid signal
  - `_ready`: ready signal
  - `_ack`: acknowledge signal
  - `_req`: request signal
  - `_done`: done signal
  - `_data`: data bus (e.g., `tx_data_i`, `mem_addr_o`)
  - `_addr`: address bus
  - `_wr`: write signal (e.g., `axi_awvalid_i`)
  - `_rd`: read signal (e.g., `axi_arvalid_i`)
  - `_sync`: signal synchronized across clock domains
- **Prefixes**:
  - `clk_`: clock signals (e.g., `clk_core`, `clk_mem`)
  - `rst_n_` or `arst_n_`: active-low asynchronous reset (project-specific choice, be consistent)
  - `srst_n_` or `rst_n_`: active-low synchronous reset (project-specific choice, be consistent)
  - `rst_p_`: active-high reset (less common for top-level resets)
- **State Machine Signals**:
  - State register: `state_r`
  - Next state logic: `state_ns`
  - State encoding: `S_IDLE`, `S_FETCH`, `S_DECODE` (use enums for states)
- **Bus Connections**: Always `[MSB:LSB]` (e.g., `logic [31:0] data_bus;`)

### 2.5. Parameters and Localparams
- UPPER_CASE_SNAKE_CASE (e.g., `DATA_WIDTH`, `FIFO_DEPTH`).
- **Parameter Classification and Naming**:
  - a) **Configurable Parameters** (can be overridden during instantiation):
    - Prefix: `CONFIG_` for module parameters (e.g., `CONFIG_DATA_WIDTH`, `CONFIG_FIFO_DEPTH`)
  - b) **Design Constants** (fixed values, not meant to be overridden):
    - Prefix: `CONST_` for constants (e.g., `CONST_AXI_BURST_INCR`, `CONST_RESET_CYCLES`)
  - c) **Local Parameters** (derived or internal constants):
    - Prefix: `LP_` for localparams (e.g., `LP_ADDR_BITS`, `LP_COUNT_WIDTH`)
  - d) **Type Parameters**:
    - Prefix: `TYPE_` for type parameters (e.g., `TYPE_ADDR`, `TYPE_DATA`)

### 2.6. Type Definitions (typedefs, enums, structs)
- **typedefs**: uses snake_case with `_t` suffix (e.g., `address_t`, `state_type_t`, `config_bus_t`).
- **enums**: uses snake_case with `_e` suffix (e.g., `color_e`, `machine_fsm_e`).
- **structs**: uses snake_case with `_s` suffix (e.g., `write_addr_s`, `read_resp_s`)

### 2.7. FSM State Naming (Special Case)
- FSM states should use simple descriptive names with `S_` prefix (e.g., `S_IDLE`, `S_ACTIVE`).
- Do NOT use `CONST_` prefix for FSM states.
- Prefer using enums for state definitions: `typedef enum logic [1:0] { S_IDLE, S_ACTIVE, S_DONE } state_e;`

### 2.8. Instances
- `u_<ModuleName>` or `<module_name_instance_purpose>` (e.g., `u_data_fifo`, `data_path_fifo`). Be consistent.

### 2.9. Generate Blocks
- `gen_<purpose>` (e.g., `gen_lanes[i].u_LaneLogic`).
- Ensure that there is no generate block labels that are identical.

### 2.10. Assertions and Sequences
- `assert_<property_name>` for assertions.
- `seq_<sequence_name>` for sequences.
- `prop_<property_name>` for properties.
- `cg_<group_name>` for covergroups.
- `cp_<point_name>` for coverpoints.

---

## 3. Directory Structure

A well-organized directory structure is critical for managing a complex chip design project. The following structure is recommended as a standard template.

```
project_root/
├── asic/
│   ├── constraints/      // ASIC-specific timing and physical constraints
│   ├── pnr/              // Place and Route scripts and results
│   └── reports/          // ASIC-specific reports (timing, power, area)
│
├── cdc/                  // Clock Domain Crossing (CDC) analysis
│   ├── scripts/          // CDC tool scripts
│   ├── reports/          // CDC reports
│   └── waivers/          // CDC waivers and justifications
│
├── docs/                 // Design documents, specifications, and user guides
│
├── formal/               // Formal verification scripts, properties, and reports
│
├── fpga/
│   ├── constraints/      // FPGA-specific timing and pin constraints
│   ├── bitstreams/       // Compiled FPGA bitstream files
│   └── reports/          // FPGA-specific reports (utilization, timing)
│
├── lint/                 // Linting scripts, reports, and configuration
│   ├── scripts/          // Lint tool scripts
│   ├── reports/          // Lint reports
│   └── waivers/          // Lint rule waivers
│
├── rtl/                  // All synthesizable SystemVerilog RTL code (.sv)
│   ├── config/           // Configuration packages and parameter definitions
│   ├── core/             // Main processor core logic
│   │   ├── control/      // Control logic, hazard detection, instruction decoding
│   │   ├── execution/    // Execution units (ALU, MUL, DIV)
│   │   ├── pipeline/     // Pipeline stages (fetch, decode, execute, memory, writeback)
│   │   └── prediction/   // Branch prediction logic
│   ├── interfaces/       // Standard bus and communication interface definitions
│   ├── memory/           // Memory subsystem, including caches and controllers
│   │   ├── cache/        // Cache modules (I-Cache, D-Cache, L2, L3)
│   │   └── coherency/    // Cache coherency logic (e.g., MESI protocol)
│   ├── peripherals/      // Peripheral IP cores (UART, SPI, GPIO)
│   ├── power/            // Power management units and logic
│   ├── protocol/         // Protocol adapters and arbiters (AXI, TileLink, CHI)
│   └── shared/           // Modules and packages shared across the design
│       └── packages/     // Shared type definitions, constants, and functions
│
├── scripts/              // General utility and automation scripts (lint, build, etc.)
│
├── sim/                  // Simulation scripts, makefiles, and run directories
│
├── software/             // C/C++ and assembly code for on-chip execution and testing
│   ├── bootloader/       // First-stage boot code
│   └── tests/            // Bare-metal tests and benchmarks
│
├── sub/                  // Git submodules for external IPs or shared libraries (often in detached HEAD state)
│
├── syn/                  // Synthesis scripts, general constraints, and reports
│   ├── scripts/          // Synthesis scripts for various tools
│   ├── constraints/      // General (non-ASIC/FPGA) timing constraints
│   └── reports/          // General synthesis reports
│
├── tb/                   // Testbench and verification environment
│   ├── common/           // Common verification components (checkers, drivers, monitors)
│   ├── integration/      // Integration-level testbenches
│   ├── unit/             // Unit-level testbenches for individual modules
│   └── vip/              // Third-party Verification IP
│
└── tools/                // Project-specific helper tools or configuration files

```

---

## 4. Module and Interface Declarations

### 4.1. File Header
- Every `.sv` and `.svh` file must start with a standard header.

  ```systemverilog
  //=============================================================================
  // Company: <Company Name>
  // Project Name: <ProjectName>
  //
  // File: <FileName.sv>
  //
  // ----- Fields for Automated Documentation -----
  // MODULE_NAME: <ModuleName>
  // AUTHOR: <Author Name> (<author_email@company.com>)
  // VERSION: <X.Y.Z>
  // DATE: <YYYY-MM-DD>
  // DESCRIPTION: <Brief, single-line description of the module's purpose.>
  // PRIMARY_PURPOSE: <Detailed purpose of the module.>
  // ROLE_IN_SYSTEM: <How this module fits into a larger system.>
  // PROBLEM_SOLVED: <What specific problem this module addresses.>
  // MODULE_TYPE: <e.g., RTL, Behavioral, Testbench_Component>
  // TARGET_TECHNOLOGY_PREF: <ASIC/FPGA>
  // RELATED_SPECIFICATION: <Document_Name_Or_Link_to_Spec>
  //
  // ----- Status and Tracking -----
  // VERIFICATION_STATUS: <Not Verified | In Progress | Verified | Formally Verified>
  // QUALITY_STATUS: <Draft | Reviewed | Approved | Released>
  //
  //=============================================================================
  //
  `timescale 1ns/1ps
  `default_nettype none
  //
  ```

### 4.1.1 File Footer
- Every `.sv` and `.svh` file must end with a standard footer.

  ```systemverilog
  //=============================================================================
  // Dependencies: <list of dependencies>
  //
  // Instantiated In:
  //   - core/integration/some_subsystem.sv
  //   - memory/controller/another_module.sv
  //
  // Performance:
  //   - Critical Path: <expected critical path>
  //   - Max Frequency: <range of frequency>
  //   - Area: <rough estimate>
  //
  // Verification Coverage:
  //   - Code Coverage: <Coverage from tool>
  //   - Functional Coverage: <Coverage from tool>
  //   - Branch Coverage: <Coverage from tool>
  //
  // Synthesis:
  //   - Target Technology: ASIC/FPGA
  //   - Synthesis Tool: Design Compiler/Quartus
  //   - Clock Domains: <number of clk domain>
  //   - Constraints File: <SDC file name>
  //
  // Testing:
  //   - Testbench: <testbench name>
  //   - Test Vectors: <number of test vectors in testbench mentioned above>
  //
  //----
  // Revision History:
  // Version | Date       | Author             | Description
  //=============================================================================
  // 1.1.0   | YYYY-MM-DD | <Author Name>      | Added X / Implemented Y (Summary of changes)
  // 1.0.0   | YYYY-MM-DD | <Author Name>      | Initial release
  //=============================================================================
  ```

### 4.2. Module Definition
- Use ANSI-style port declarations.
- Parameters must explicitly be typed.
- Group and align ports for readability.
- Only declare 1 port or signal name per line.

  ```systemverilog
  module MyModule #(
      // Configurable Parameters (design-time configurable)
      parameter integer CONFIG_DATA_WIDTH     = 32,    // Input/output data bus width
      parameter integer CONFIG_FIFO_DEPTH     = 1024,  // Internal FIFO storage depth
      parameter integer CONFIG_NUM_CHANNELS   = 4,     // Number of parallel channels
      
      // Type Parameters
      parameter type    TYPE_ADDR          = logic [15:0], // Address type definition
      parameter type    TYPE_USER          = logic [7:0],  // User-defined signal type
      
      // Design Constants (architectural constants)
      parameter integer CONST_PIPELINE_STAGES = 3,    // Fixed number of pipeline stages
      parameter integer CONST_RESET_CYCLES    = 10    // Reset synchronization cycles
  ) (
      // Clock and Reset
      input  logic                clk_i,         // System clock
      input  logic                rst_ni,        // Asynchronous active-low reset

      // Data Input Interface
      input  logic [CONFIG_DATA_WIDTH-1:0] din_data_i,
      input  logic                         din_valid_i,
      output logic                         din_ready_o,

      // Control Signals
      input  logic                enable_processing_i,
      output logic                processing_done_o,

      // Data Output Interface
      output logic [CONFIG_DATA_WIDTH-1:0] dout_data_o,
      output logic                         dout_valid_o,
      input  logic                         dout_ready_i
  );

      // ----- Local Parameters -----
      // Define derived parameters here.
      // See Section 2.5 for naming conventions (e.g., LP_... prefix).
      // See Section 10.2 for avoiding "magic numbers".

      // ----- Internal Signal Declarations -----
      // Declare all internal registers, wires, and state variables here.
      // See Section 2.4 for signal naming conventions (e.g., _r, _c, _ns suffixes).

      // ----- Combinational Logic -----
      // Implement combinational logic using `always_comb`.
      // See Section 9 for guidelines on preventing latches by using default assignments.
      // `assign` statements are also used here for simple combinational logic.

      // ----- Sequential Logic (Registers) -----
      // Implement all flip-flops using `always_ff`.
      // See Section 6.1 for the mandatory reset strategy.

      // ----- Finite State Machine (FSM) -----
      // Implement FSMs using the two-process style.
      // See Section 7 for detailed FSM design guidelines, including the use
      // of a `default` case and safe state recovery.

      // ----- Sub-module Instantiations -----
      // Instantiate any sub-modules here.
      // See Section 5.5 for rules on named port connections.

      // ----- Assertions -----
      // Add concurrent assertions to verify module properties.
      // See Section 11 for guidelines on integrated verification.

  endmodule : MyModule
  // `default_nettype wire // Revert default_nettype if absolutely necessary for legacy code,
                         // but prefer keeping `none` throughout the project and explicitly
                         // typing all signals. If reverted, do it at the end of the file.
  ```

### 4.3. Interface Definition
- Use modports to define perspectives (e.g., master, slave, monitor).
- Only declare 1 port or signal name per line.

  ```systemverilog
  interface MyBus_if #(
      // Configurable Parameters
      parameter integer CONFIG_DATA_WIDTH = 32,  // Data bus width
      parameter integer CONFIG_ADDR_WIDTH = 16   // Address bus width
  ) (
      input logic clk,
      input logic rst_n
  );
      logic [CONFIG_ADDR_WIDTH-1:0] addr;
      logic [CONFIG_DATA_WIDTH-1:0] wdata;
      logic [CONFIG_DATA_WIDTH-1:0] rdata;
      logic                  write_en;
      logic                  read_en;
      logic                  ready;
      logic                  valid;

      modport Master (
          output addr, wdata, write_en, read_en,
          input  rdata, ready, valid,
          input  clk, rst_n
      );

      modport Slave (
          input  addr, wdata, write_en, read_en,
          output rdata, ready, valid,
          input  clk, rst_n
      );

      modport Monitor (
          input addr, wdata, rdata, write_en, read_en, ready, valid,
          input clk, rst_n
      );
  endinterface : MyBus_if
  ```

---

## 5. RTL Coding Style

### 5.1. Data Types
- Use `logic` for general-purpose signals. Avoid `wire` and `reg`.
- Use `bit` for 2-state variables where appropriate.
- Use packed structures (`struct packed`) and packed arrays for bit-level concatenation.
- Use `enum` for FSM states and named constants.

### 5.2. Procedural Blocks
- `always_comb`: For purely combinational logic.
- `always_ff`: For sequential logic (flip-flops).
- `always_latch`: For intentional latches (use with caution).
- **`initial` Blocks**: All `initial` statements must be enclosed in an `` `ifndef SYNTHESIS `` construct. This is critical for preventing synthesis tools from misinterpreting simulation-only constructs, which can lead to errors or unintended behavior.
  ```systemverilog
  // Correct: initial block protected from synthesis
  `ifndef SYNTHESIS
  initial begin
      // This block is for simulation only, e.g., initializing memory
      $readmemh("mem_init.hex", rtl_memory);
  end
  `endif
  ```

### 5.3. Assignments
- Use non-blocking assignments (`<=`) in `always_ff`.
- Use blocking assignments (`=`) in `always_comb` and for variable assignments.

### 5.4. Operators
- Use `===` and `!==` for case equality comparison (4-state logic).
- Use `==` and `!=` for 2-state logic or where X/Z propagation is not a concern.

### 5.5. Instantiation
- Use named port connections (`.port_name(signal_name)`). Avoid positional connections.

### 5.6. Generate Blocks
- Use `generate` constructs for creating regular, repeated, or conditionally instantiated structures to improve code parameterization and maintainability.
- Per the IEEE standard, `generate` keywords must be used with a conditional construct (`if`/`case`) or a loop (`for`). Standalone `generate`...`endgenerate` wrappers are not the intended use and must be avoided.
- All generate blocks created by a loop **must** include a `begin`...`end` block, and this block **must** be named. This is critical for debugging and referencing the generated hierarchy.

  ```systemverilog
  // GOOD: `for-generate` block with a named begin...end
  gen_lanes: for (genvar i = 0; i < CONFIG_NUM_LANES; i++) begin : B_LANE
      // Instantiated logic for each lane
      lane_logic u_lane_logic (
          .clk_i      (clk_i),
          .rst_ni     (rst_ni),
          .data_in_i  (data_bus_i[i]),
          .data_out_o (data_bus_o[i])
      );
  end : B_LANE

  // GOOD: `if-generate` block with a named begin...end
  if (CONFIG_HAS_FEATURE_X) begin : B_FEATURE_X
      feature_x_module u_feature_x (
          // ... connections
      );
  end : B_FEATURE_X

  // BAD: Standalone generate block (Functionally useless and prohibited)
  // generate
  //    my_module u_my_module(...);
  // endgenerate
  ```

### 5.7. Packages
- Use packages (`package`...`endpackage`) to share parameters, types, and functions across modules.
- Import specific items: `import my_pkg::my_type;` or use a wildcard `import my_pkg::*;`.

---

## 6. Clocking and Reset Strategy

A robust clocking and reset strategy is fundamental to a stable design.

### 6.1. Reset Strategy
- The project-wide standard is an **active-low, asynchronous-assertion, synchronous-deassertion** reset.
- **Asynchronous Assertion**: The reset can be asserted at any time to force the design into a known state immediately, regardless of clock stability.
- **Synchronous De-assertion**: The reset signal must be synchronized to the clock domain it is resetting before being de-asserted. This prevents metastability that can occur if the reset is removed close to an active clock edge.
- A standard reset synchronizer module from the shared library must be used for this purpose.

### 6.2. Clock Gating
- Use tool-integrated clock gating cells (e.g., ICG cells) whenever possible instead of custom RTL implementations.
- Manual clock gating with `AND`/`OR` gates is strictly discouraged as it is prone to glitches and timing issues.

### 6.3. Handling Multiple Clocks
- Signals that cross between different clock domains must be treated with extreme care.
- Never assign a signal from one clock domain directly to a signal in another.
- Always use approved CDC techniques as detailed in Section 8.

---

## 7. Finite State Machine (FSM) Design Guidelines

To ensure FSMs are readable, maintainable, and robust, the following guidelines are mandatory.

### 7.1. Recommended Implementation Style
- All FSMs must be implemented using a **two-process style**:
  1.  **Combinational Process (`always_comb`)**: This block calculates the next state and any combinational outputs based on the current state and inputs.
  2.  **Sequential Process (`always_ff`)**: This block registers the next state value to the current state register on the clock edge.

  ```systemverilog
  // Good example of a two-process FSM
  // State Register (Sequential)
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_fsm_state_reg
      if (!rst_ni) begin
          current_state_r <= S_IDLE;
      end else begin
          current_state_r <= next_state_c;
      end
  end

  // Next-State and Output Logic (Combinational)
  always_comb begin : proc_fsm_next_state
      // Default assignments to avoid latches
      next_state_c = current_state_r;
      my_output_c = 1'b0;

      case (current_state_r)
          S_IDLE: begin
              if (start_i) begin
                  next_state_c = S_WORKING;
              end
          end
          S_WORKING: begin
              my_output_c = 1'b1;
              if (done_i) begin
                  next_state_c = S_IDLE;
              end
          end
          default: begin
              next_state_c = S_IDLE;
          end
      endcase
  end
  ```

### 7.2. Safe FSM Practices
- Every FSM `case` statement **must** include a `default` case.
- The `default` case should transition the FSM to a known safe state (e.g., the idle or reset state) to ensure the machine can recover from any unforeseen or illegal state.

---

## 8. Clock Domain Crossing (CDC) Best Practices

Improperly handled CDC is a primary source of functional failures in multi-clock designs.

### 8.1. Use Standardized Synchronizers
- **Manual CDC logic is forbidden.**
- All signals crossing clock domains must use a pre-verified, standardized synchronizer module from a shared project library.
- **For single-bit control signals**: Use a 2-flop or 3-flop synchronizer.
- **For multi-bit data buses**: Use an asynchronous FIFO (Async FIFO).
- **For multi-bit control buses**: Use a handshake-based synchronizer protocol.

### 8.2. Prohibit Direct Cross-Domain Assignments
- Direct assignment of a signal from one clock domain to another is a critical design error and is strictly prohibited.
  ```systemverilog
  // BAD: Do NOT do this if clk_a and clk_b are different clocks
  always_ff @(posedge clk_b) begin
      signal_in_b_domain_r <= signal_from_a_domain;
  end
  ```

### 8.3. Verification
- All CDC paths must be identified and formally verified using a dedicated CDC analysis tool.
- Any waivers must be explicitly documented and rigorously reviewed.

---

## 9. Guidelines for Preventing Latches

Unintended latches are a common RTL bug that can lead to timing issues and functional errors.

### 9.1. Default Assignments in Combinational Logic
- The most robust method to prevent latches is to provide a default assignment for all signals that are assigned within an `always_comb` block.
- This assignment must be made at the beginning of the block, before any conditional logic (`if`, `case`).

  ```systemverilog
  // GOOD: Prevents latches with default assignments
  always_comb begin
      // Default assignments at the top
      next_state_c = current_state_r;
      data_out_c = '0;
      valid_out_c = 1'b0;

      if (enable_i) begin
          data_out_c = data_in_i;
          if (condition_a) begin
              valid_out_c = 1'b1;
          end
      end
  end

  // BAD: Prone to creating latches
  always_comb begin
      // No default assignments. If enable_i is false,
      // data_out_c and valid_out_c are not assigned, creating latches.
      if (enable_i) begin
          data_out_c = data_in_i;
          if (condition_a) begin
              valid_out_c = 1'b1;
          end
      end
  end
  ```

### 9.2. Fully Specified Conditional Logic
- As an alternative to default assignments, you must ensure that all signals are assigned a value in every possible branch of an `if`/`else` or `case` statement.
- This is less robust and harder to maintain than the default assignment method, which is the preferred style.

---

## 10. Code Reusability and Configurability

To maximize the value of our IP, modules should be designed for reuse from the outset.

### 10.1. Parameterize Everything
- All key architectural features of a module **must** be defined as parameters. This includes, but is not limited to:
  - Data and address bus widths
  - FIFO depths and memory sizes
  - Number of channels, ports, or instances
  - Timeout counters or pipeline stage counts
- This practice allows a single module to be easily configured for different use cases without modifying the underlying RTL.

### 10.2. Avoid "Magic Numbers"
- Hard-coding constants directly in the logic is strictly prohibited.
- Use `localparam` to define derived values or internal constants that are calculated from parameters. This keeps the logic clean and ensures that dependent values update automatically when a parameter is changed.

  ```systemverilog
  // GOOD: Derived values are calculated with localparam
  parameter integer CONFIG_FIFO_DEPTH = 512;
  localparam integer LP_ADDR_WIDTH = $clog2(CONFIG_FIFO_DEPTH);
  // ...
  logic [LP_ADDR_WIDTH-1:0] fifo_addr;

  // BAD: Magic numbers are hard-coded
  logic [8:0] fifo_addr; // Why 9 bits? What if FIFO depth changes?
  ```

---

## 11. Integrated Verification with Assertions

Verification is a core part of the design process, not a separate step. Embedding verification logic within the design is mandatory.

### 11.1. Assert Critical Properties
- Key assumptions, state invariants, and protocol behaviors **must** be formally captured using SystemVerilog Assertions (SVA).
- Examples of properties to assert include:
  - FSM state transitions (e.g., `assert property (@(posedge clk) !(current_state_r == S_A && next_state_c == S_C));`)
  - One-hot state encoding invariants (`assert property (@(posedge clk) $onehot(state_vector_r));`)
  - Handshake protocol rules (e.g., a `valid` signal must remain high until `ready` is asserted).
  - Bus protocol compliance.

### 11.2. Assertions for Simulation and Formal
- These assertions serve a dual purpose: they are checked during simulation runs to catch bugs early, and they can be used as properties for formal verification tools.

---

## 12. High-Quality Inline Commenting

Clear comments are essential for long-term maintainability.

### 12.1. Comment the "Why," Not the "What"
- The code itself describes *what* is happening. A good comment explains *why* it is happening.
- Use comments to clarify design intent, explain a non-obvious implementation choice, or highlight a necessary trade-off.

  ```systemverilog
  // BAD: Redundant comment that explains nothing
  // Increment the counter
  counter_r <= counter_r + 1;

  // GOOD: Explains the design intent
  // The FIFO pointer wraps around after reaching the max depth.
  // The extra +1 is to account for the read/write domain synchronization delay.
  if (pointer_r == MAX_DEPTH + 1) begin
      pointer_r <= '0;
  end
  ```

---

## 13. Performance and Area Considerations

RTL design is not just about function; it's about meeting performance, power, and area (PPA) targets.

### 13.1. Identify Critical Paths
- When a known critical path exists in a module, it should be explicitly noted in the comments near the relevant logic. This helps focus optimization efforts and alerts future engineers to sensitive timing paths.

### 13.2. Document PPA Assumptions
- If a module is designed with specific performance or area targets in mind, these should be noted in the module's file header. This includes target frequency, expected area, or power constraints.

### 13.3. Pipelining Strategy
- For high-speed logic, pipelining is the primary technique for timing closure. The guide encourages proactive pipelining of complex combinatorial paths rather than waiting for synthesis reports to reveal timing failures.

---

## Document Information

- **Version:** 2.0
- **Last Updated:** 2025-05-25
- **Status:** Final
