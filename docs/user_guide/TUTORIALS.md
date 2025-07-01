# RISC-V Core Tutorials

This document provides a collection of tutorials to guide you through common tasks and advanced customization of the RISC-V core.

## Table of Contents

- [Introduction](#introduction)
- [Tutorial 1: Adding a Custom Instruction](#tutorial-1-adding-a-custom-instruction)
- [Tutorial 2: Integrating a New Peripheral](#tutorial-2-integrating-a-new-peripheral)
- [Tutorial 3: Analyzing Performance with Performance Monitors](#tutorial-3-analyzing-performance-with-performance-monitors)
- [Tutorial 4: Customizing the Cache Hierarchy](#tutorial-4-customizing-the-cache-hierarchy)

## Introduction

These tutorials are designed to be hands-on guides that will help you understand the internals of the RISC-V core and how to modify it for your own needs. Each tutorial provides step-by-step instructions and references the relevant source files.

## Tutorial 1: Adding a Custom Instruction

This tutorial will walk you through the process of adding a custom instruction to the RISC-V core's instruction set. We will add a simple `ADD_ACC` instruction that adds the values from two source registers (`rs1` and `rs2`) and accumulates the result into a special-purpose accumulator register within the pipeline. This instruction will follow the R-type format.

### Step 1: Define the Instruction Opcode

First, we need to define a unique opcode for our new instruction. The RISC-V ISA provides dedicated "custom" opcode space for user-defined extensions. We'll use the `custom-0` opcode (`7'b0001011`).

We'll also define a `funct7` value to distinguish our instruction from other potential custom instructions that might use the same `custom-0` opcode.

Open `rtl/shared/packages/riscv_core_types_pkg.sv` and add the following constants:

```systemverilog
// ... existing code ...
    parameter logic [6:0] OPCODE_FENCE  = 7'b0001111;
    parameter logic [6:0] OPCODE_SYSTEM = 7'b1110011;
    // Add custom opcode
    parameter logic [6:0] OPCODE_CUSTOM_0 = 7'b0001011;

    // Function codes
    parameter logic [6:0] FUNCT7_M_EXT = 7'b0000001;
    // Add funct7 for our custom instruction
    parameter logic [6:0] FUNCT7_ADD_ACC = 7'b0000010;
// ... existing code ...
```

### Step 2: Modify the Decoder

Next, we'll update the decoder in `rtl/core/pipeline/decode_stage.sv` to recognize the new instruction and generate the correct control signals. We'll add a new control signal, `acc_write_en`, to signal the execute stage to write to our new accumulator.

First, add `acc_write_en` to the `ctrl_signals_t` struct in `rtl/shared/packages/riscv_core_pkg.sv`:

```systemverilog
// ... existing code ...
    typedef struct packed {
        alu_op_e    alu_op;
        alu_a_sel_e alu_src_a_sel;
        alu_b_sel_e alu_src_b_sel;
        logic       mem_read_en;
        logic       mem_write_en;
        logic       reg_write_en;
        wb_sel_e    wb_mux_sel;
        logic       is_branch;
        logic       mult_en;
        logic       div_en;
        logic       csr_cmd_en;
        logic       acc_write_en; // New control signal
        logic [2:0] funct3;
    } ctrl_signals_t;
// ... existing code ...
```

Now, in `rtl/core/pipeline/decode_stage.sv`, update the decoder's `always_comb` block to handle the `OPCODE_CUSTOM_0`.

```systemverilog
// ... existing code ...
    always_comb begin
        // Default control signals for a bubble (NOP)
        ctrl_d.alu_op         = ALU_OP_ADD;
// ... existing code ...
        ctrl_d.csr_cmd_en     = 1'b0;
        ctrl_d.acc_write_en   = 1'b0; // Default to off
        ctrl_d.funct3         = funct3;

        // Only decode if the instruction from the fetch stage is valid
        if (if_id_reg_i.valid) begin
            case (opcode)
// ... existing code ...
                OPCODE_SYSTEM: begin
                    ctrl_d.csr_cmd_en   = 1'b1;
// ... existing code ...
                    ctrl_d.wb_mux_sel   = WB_SEL_CSR;
                end
                // Add case for our custom instruction
                OPCODE_CUSTOM_0: begin
                    if (funct7 == FUNCT7_ADD_ACC) begin
                        ctrl_d.alu_op        = ALU_OP_ADD;
                        ctrl_d.alu_src_a_sel = ALU_A_SEL_RS1;
                        ctrl_d.alu_src_b_sel = ALU_B_SEL_RS2;
                        ctrl_d.acc_write_en  = 1'b1; // Enable accumulator write
                        ctrl_d.reg_write_en  = 1'b0; // Don't write to the main register file
                    end
                end
                default:;
            endcase
        end
    end
// ... existing code ...
```

### Step 3: Update the Execution Stage

Now we need to add the accumulator register to the `execute_stage` and use the `acc_write_en` signal to control it. For simplicity in this tutorial, we will not handle pipeline hazards related to the accumulator.

In `rtl/core/pipeline/execute_stage.sv`, add the accumulator register and the logic to update it.

```systemverilog
module execute_stage
// ... module ports ...
);
// ... existing internal signals ...

    // New accumulator register
    logic [XLEN-1:0] accumulator_q;

    // ALU instantiation
    alu alu_inst (
// ... port connections ...
    );

    // In the main pipeline register block...
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            ex_mem_reg_q.ctrl.reg_write_en <= 1'b0;
            accumulator_q                  <= '0; // Reset accumulator
        end else if (!stall_e_i) begin
            // ... existing register logic ...

            // Accumulator logic
            if (id_ex_reg_i.ctrl.acc_write_en) begin
                accumulator_q <= accumulator_q + alu_result;
            end
        end
    end
// ... existing code ...
```
Since we are not writing the result back to the main register file (`GPR`), we don't need to modify the write-back stage for this simple tutorial. A real implementation might require a way to read the accumulator's value.

### Step 4: Create a Testbench

To test our new instruction, we can create a simple assembly file and a testbench.

Create `test_add_acc.s`:
```assembly
.global _start

_start:
    # Initialize registers
    li x1, 10
    li x2, 20
    li x3, 30
    li x4, 40

    # Custom instruction: add_acc x0, x1, x2 -> acc = acc + 10 + 20
    # Encoding for add_acc (custom-0, funct7=0b0000010)
    .word 0x00c5800b # funct7=0b0000010,rs2=x2,rs1=x1,funct3=0,rd=x0,opcode=custom-0

    # Custom instruction: add_acc x0, x3, x4 -> acc = acc + 30 + 40
    .word 0x018e800b # funct7=0b0000010,rs2=x4,rs1=x3,funct3=0,rd=x0,opcode=custom-0

    # The result (100) will be in the accumulator register inside the execute_stage
    # In a real scenario, you would need another custom instruction
    # to move the accumulator value to a general-purpose register
    # to verify it. For this tutorial, we would check it via waveform.

    # Infinite loop
loop:
    j loop
```

You would then need to compile this with a RISC-V toolchain, load the resulting binary into your testbench memory, and run the simulation. In the simulation, you would use your simulator's tools to inspect the value of the `accumulator_q` register inside the `execute_stage` module and verify that it equals `100` after the two custom instructions have executed. 

## Tutorial 2: Integrating a New Peripheral

This tutorial will guide you through the process of adding a simple memory-mapped peripheral to the RISC-V system. We will create a 64-bit timer that can be controlled by software.

### Step 1: Define the Peripheral's Address Range

Peripherals are accessed via memory-mapped I/O (MMIO). First, we must assign a unique address range to our new timer. The system's memory map is defined in `rtl/config/core/riscv_memory_config_pkg.sv`. We will add our timer's base address within the existing `PERIPHERAL_BASE` region.

Open `rtl/config/core/riscv_memory_config_pkg.sv` and add the timer's address constants:

```systemverilog
// ... existing code ...
    // Peripheral memory region  
    parameter logic [31:0] PERIPHERAL_BASE = 32'hF000_0000;
    parameter logic [31:0] PERIPHERAL_SIZE = 32'h1000_0000;          // 256MB peripheral space

    // Add new peripheral addresses here
    parameter logic [31:0] MMIO_TIMER_BASE_ADDR = PERIPHERAL_BASE + 32'h0000_1000;
    parameter logic [31:0] MMIO_TIMER_END_ADDR  = MMIO_TIMER_BASE_ADDR + 32'hF; // 16 bytes for our timer
// ... existing code ...
```

### Step 2: Create the Peripheral Module

Next, we'll create the SystemVerilog module for our timer. This timer will have a 64-bit counter that increments on every clock cycle when enabled, and two memory-mapped registers:
-   **`CTRL` (Control Register) at offset `0x0`**:
    -   `[0]`: `enable` (1 to enable, 0 to disable)
    -   `[1]`: `reset` (1 to reset the counter to 0)
-   **`VALUE` (Counter Value) at offset `0x8`**: A read-only register to get the current 64-bit counter value.

Create a new file `rtl/units/simple_timer.sv`:

```systemverilog
// rtl/units/simple_timer.sv
`timescale 1ns/1ps
`default_nettype none

module simple_timer (
    input  logic        clk_i,
    input  logic        rst_ni,

    // Memory-mapped interface
    input  logic        req_valid_i,
    output logic        req_ready_o,
    input  logic        req_write_i,
    input  logic [3:0]  req_addr_i,  // Address within the timer (offset)
    input  logic [31:0] req_wdata_i,
    output logic [31:0] req_rdata_o
);

    logic [63:0] counter_q;
    logic        enable_q;

    assign req_ready_o = 1'b1; // Always ready to accept requests

    // Register write logic
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            counter_q <= '0;
            enable_q  <= 1'b0;
        end else begin
            if (req_valid_i && req_write_i && req_addr_i == 4'h0) begin
                enable_q <= req_wdata_i[0];
                if (req_wdata_i[1]) begin
                    counter_q <= '0;
                end
            end

            if (enable_q) begin
                counter_q <= counter_q + 1;
            end
        end
    end

    // Register read logic
    always_comb begin
        req_rdata_o = '0;
        if (req_valid_i && !req_write_i) begin
            case (req_addr_i)
                4'h0: req_rdata_o = {31'b0, enable_q};
                4'h8: req_rdata_o = counter_q[31:0];
                4'hC: req_rdata_o = counter_q[63:32];
                default: req_rdata_o = '0;
            endcase
        end
    end

endmodule
```

### Step 3: Integrate the Peripheral into the System

Now we must instantiate our timer and connect it to the memory system. The address decoding happens in `rtl/core/integration/multi_core_system.sv`. We need to modify this file to route memory requests to our timer when the address falls within its range.

Open `rtl/core/integration/multi_core_system.sv` and perform the following modifications:

1.  **Add signals** for the timer interface.
2.  **Instantiate** the `simple_timer`.
3.  **Modify the address decoder** to route requests.

```systemverilog
// In multi_core_system.sv

// ... inside module declaration ...
    // ... existing signals ...

    // Signals for our new timer peripheral
    logic        timer_req_valid;
    logic        timer_req_ready;
    logic        timer_req_write;
    logic [3:0]  timer_req_addr;
    logic [31:0] timer_req_wdata;
    logic [31:0] timer_req_rdata;

    // ... existing instantiations ...

    // Instantiate the simple_timer
    simple_timer timer_inst (
        .clk_i        (clk_i),
        .rst_ni       (rst_ni),
        .req_valid_i  (timer_req_valid),
        .req_ready_o  (timer_req_ready),
        .req_write_i  (timer_req_write),
        .req_addr_i   (timer_req_addr),
        .req_wdata_i  (timer_req_wdata),
        .req_rdata_o  (timer_req_rdata)
    );

    // Find the memory routing logic. It will be inside a generate block
    // and an always_comb block that handles memory requests.
    // Modify it to decode the timer's address.

    // This is a conceptual example. The exact logic in your file might differ.
    // Find where `l2_if[i].req_valid` is assigned.
    always_comb begin
        // ... existing logic ...

        logic is_timer_access;
        is_timer_access = (data_req.addr >= MMIO_TIMER_BASE_ADDR) &&
                          (data_req.addr <= MMIO_TIMER_END_ADDR);
        
        // Default assignments
        l2_if[i].req_valid = ...; // Existing logic
        peripheral_if[i].req_valid = 1'b0; // Assuming a peripheral bus interface
        timer_req_valid = 1'b0;

        // ... existing arbitration logic ...

        if (is_timer_access) begin
            // This is a request for our timer
            timer_req_valid   = data_req_valid;
            timer_req_write   = data_req.write;
            timer_req_addr    = data_req.addr[3:0];
            timer_req_wdata   = data_req.data;
            data_rsp.data     = timer_req_rdata;
            data_rsp_valid    = timer_req_ready; // Simplified handshake
        end else {
            // Route to L2 cache or other peripherals
            l2_if[i].req_valid = data_req_valid;
            // ... other connections ...
        }
    end
```
**Note:** The address decoding logic can be complex. The example above is simplified. You need to find the correct place in `multi_core_system.sv` where the data memory request is routed based on its address and insert the logic to handle the timer's address range.

### Step 4: Write Software to Use the Timer

Finally, you can write a simple C program to interact with the timer. This program will enable the timer, wait for some time, and then read the counter value.

```c
#include <stdint.h>

#define TIMER_BASE_ADDR 0xF0001000
#define TIMER_CTRL_REG  (volatile uint32_t*)(TIMER_BASE_ADDR + 0x0)
#define TIMER_VAL_LOW   (volatile uint32_t*)(TIMER_BASE_ADDR + 0x8)
#define TIMER_VAL_HIGH  (volatile uint32_t*)(TIMER_BASE_ADDR + 0xC)

int main() {
    // Enable the timer
    *TIMER_CTRL_REG = 0x1;

    // Wait for a bit (just a dummy loop)
    for (int i = 0; i < 10000; i++) {
        asm volatile("nop");
    }

    // Read the 64-bit timer value
    uint32_t low = *TIMER_VAL_LOW;
    uint32_t high = *TIMER_VAL_HIGH;
    uint64_t value = ((uint64_t)high << 32) | low;

    // Disable the timer
    *TIMER_CTRL_REG = 0x0;

    // To verify, you would typically print the value,
    // but in a bare-metal environment, you might write it
    // to another peripheral like a UART, or just halt
    // and check the value in a debugger.

    while(1);

    return 0;
}
```

This completes the tutorial on integrating a new peripheral. The key steps are defining the memory map, creating the hardware, integrating it into the system's address decoder, and finally, controlling it with software. 

## Tutorial 3: Analyzing Performance with Performance Monitors

This tutorial explains how to use the built-in performance counters to measure the performance of your software running on the RISC-V core. We will focus on the two most fundamental performance counters: `mcycle` (machine cycles) and `minstret` (instructions retired).

### Step 1: Understanding the Performance Counters

The RISC-V specification includes standard CSRs for performance monitoring. We have implemented the following 64-bit counters:

-   **`mcycle` (CSR address `0xB00`)**: This counter increments on every clock cycle. It measures the total time elapsed.
-   **`minstret` (CSR address `0xB02`)**: This counter increments for every instruction that successfully completes execution (retires). It measures the amount of work done.

These counters are implemented in `rtl/units/csr_regfile.sv`. They are read-only and free-running, meaning they start counting from reset and cannot be written to by software.

To read these 64-bit counters on a 32-bit architecture (RV32), you must read the high and low words separately. The standard CSR addresses are:
-   `mcycle` (low 32 bits): `0xB00`
-   `mcycleh` (high 32 bits): `0xB80`
-   `minstret` (low 32 bits): `0xB02`
-   `minstreth` (high 32 bits): `0xB82`

The hardware ensures that a read of the low-word register followed by a read of the high-word register will provide a consistent 64-bit snapshot.

### Step 2: Writing Software to Read the Counters

You can access these counters from C code using inline assembly. Here is a helper function to read a 64-bit CSR:

```c
#include <stdint.h>

// Function to read a 64-bit performance counter
static inline uint64_t read_csr_64(int csr_num_low, int csr_num_high) {
    uint32_t high, low, high2;
    uint64_t value;

    // The standard recommends a specific read sequence to ensure
    // that the 64-bit value is read atomically even if an
    // overflow occurs between the two 32-bit reads.
    do {
        asm volatile ("rdcycleh %0" : "=r"(high));
        asm volatile ("rdcycle %0"  : "=r"(low));
        asm volatile ("rdcycleh %0" : "=r"(high2));
    } while (high != high2);

    value = ((uint64_t)high << 32) | low;
    return value;
}

// Helper functions for specific counters
uint64_t get_cycles() {
    // We use the same sequence for minstret, just with different CSRs
    // but for simplicity, we show the direct CSR numbers here.
    // The inline assembly `rdcycle` and `rdcycleh` maps to the
    // correct CSRs (mcycle and mcycleh).
    uint32_t high, low, high2;
    do {
        asm volatile ("csrr %0, mcycleh" : "=r"(high));
        asm volatile ("csrr %0, mcycle"  : "=r"(low));
        asm volatile ("csrr %0, mcycleh" : "=r"(high2));
    } while (high != high2);
    return ((uint64_t)high << 32) | low;
}

uint64_t get_instructions() {
    uint32_t high, low, high2;
    do {
        asm volatile ("csrr %0, minstreth" : "=r"(high));
        asm volatile ("csrr %0, minstret"  : "=r"(low));
        asm volatile ("csrr %0, minstreth" : "=r"(high2));
    } while (high != high2);
    return ((uint64_t)high << 32) | low;
}
```
*Note: The `rdcycle` and `rdcycleh` pseudo-instructions are standard in RISC-V toolchains and map to reads of the `mcycle` and `mcycleh` CSRs.*

### Step 3: Measuring Performance (IPC)

The most common performance metric is Instructions Per Cycle (IPC). It tells you how many instructions, on average, the core is completing in each clock cycle. An IPC greater than 1.0 is a sign of a high-performance, superscalar processor.

Here is an example of how to measure the IPC of a block of code:

```c
// A function whose performance we want to measure
void work_to_be_done() {
    volatile int a = 0;
    for (int i = 0; i < 1000; i++) {
        a += i * i;
    }
}

int main() {
    // --- Performance Measurement ---
    uint64_t start_cycles, end_cycles;
    uint64_t start_insts, end_insts;

    // Get the counter values before the work
    start_cycles = get_cycles();
    start_insts = get_instructions();

    // Call the function to be measured
    work_to_be_done();

    // Get the counter values after the work
    end_cycles = get_cycles();
    end_insts = get_instructions();
    // --- End of Measurement ---


    // --- Calculate and Report Results ---
    uint64_t cycles_elapsed = end_cycles - start_cycles;
    uint64_t insts_retired = end_insts - start_insts;

    // To calculate IPC, we use fixed-point arithmetic to avoid floating-point
    // which may not be available in an embedded context.
    // IPC = (Instructions / Cycles)
    // We calculate (Instructions * 1000) / Cycles to get IPC * 1000
    uint32_t ipc_scaled = 0;
    if (cycles_elapsed > 0) {
        ipc_scaled = (uint32_t)((insts_retired * 1000) / cycles_elapsed);
    }
    
    // In a real application, you would print these values to a UART.
    // For now, you can view them in a debugger.
    // Example: if ipc_scaled is 850, the IPC is 0.85

    while(1);
    return 0;
}
```
By reading the cycle and instruction counters before and after executing a piece of code, you can calculate its IPC and gain valuable insight into its performance on the hardware. 