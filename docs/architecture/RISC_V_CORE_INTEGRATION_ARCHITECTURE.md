# RISC-V Core Integration Architecture

## 1. Overview
This document describes the top-level integration of the RISC-V RV32IM core, focusing on how individual pipeline stages and functional units are connected to form a complete processor. The `riscv_core.sv` module serves as the central integration point, orchestrating the data flow and control signals across the entire pipeline.

## 2. Top-Level Module: `riscv_core.sv`

`riscv_core.sv` is the main module that instantiates and connects all the sub-modules representing the pipeline stages and other key functional units. It acts as the glue logic, ensuring proper communication and synchronization between different parts of the processor.

### 2.1. Key Responsibilities of `riscv_core.sv`
- **Module Instantiation**: Instantiates `fetch_stage`, `decode_stage`, `execute_stage`, `mem_stage`, `writeback_stage`, and other necessary functional units (e.g., `hazard_unit`, `csr_regfile`).
- **Pipeline Register Management**: Manages the pipeline registers (IF/ID, ID/EX, EX/MEM, MEM/WB) that transfer data and control signals between adjacent stages.
- **Inter-Stage Connections**: Connects the outputs of one stage to the inputs of the next stage, ensuring correct data and control signal propagation.
- **Hazard Control Integration**: Integrates the hazard unit to receive stall and flush signals and propagate them upstream to control pipeline flow.
- **Exception Handling Integration**: Connects exception signals from various stages to the central exception handler and manages PC redirection on traps.
- **Memory Interface Management**: Provides the top-level interfaces for instruction and data memory access, connecting them to the respective cache/memory wrapper modules.
- **CSR File Integration**: Connects the CSR file for managing control and status registers.

### 2.2. Internal Structure and Implementation Nuances

`riscv_core.sv` utilizes a `generate` block to support both single-core and multi-core configurations, allowing for flexible system scaling.

#### 2.2.1. Multi-Core System Generation (`CORE_MODE == "MULTI_CORE"`)

When configured for multi-core operation, the `riscv_core.sv` instantiates the following key components:

-   **Inter-Core Communication Interfaces**: Instances of `cache_coherency_if`, `inter_core_comm_if`, and `sync_primitives_if` are created to facilitate communication and synchronization between multiple cores.
-   **Multi-Level Cache Hierarchy**: 
    -   `l2_cache`: Instantiated to serve as a shared L2 cache for all cores. It connects to the L1 caches of individual cores and to the L3 cache.
    -   `l3_cache`: Instantiated as the last-level cache, connecting the L2 cache to the unified external memory interface (`mem_if`).
    -   `cache_coherency_controller`: Manages cache coherency (e.g., MESI protocol) across all L1 and L2 caches.
    -   `prefetch_unit`: Integrated to enhance memory performance by prefetching data.
-   **Core Manager (`core_manager`)**: A central unit responsible for managing inter-core communication and synchronization primitives across the multi-core system.
-   **Core Generation Loop**: A `genvar` loop instantiates `NUM_CORES` instances of `core_subsystem`. Each `core_subsystem` represents a full RISC-V core with its dedicated L1 instruction and data caches, and connects to the shared multi-core infrastructure (L2 cache, inter-core communication, synchronization interfaces).

#### 2.2.2. Single-Core System Generation (`CORE_MODE == "SINGLE_CORE"`)

For single-core operation, a simplified memory hierarchy is instantiated:

-   **Memory Wrapper (`memory_wrapper`)**: A basic memory wrapper is used to connect the single core's L1 instruction and data caches directly to the unified external memory interface (`mem_if`). In this mode, L2 and L3 caches are typically not instantiated.
-   **Single Core Subsystem**: A single instance of `core_subsystem` is instantiated, representing the standalone RISC-V core. Multi-core specific interfaces (inter-core communication, synchronization) are tied off or left unconnected.

## 3. Pipeline Stage Integration

The core implements a classic 5-stage pipeline:

```
┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐
│  Fetch  │───▶│ Decode  │───▶│Execute  │───▶│ Memory  │───▶│Writeback│
│  Stage  │    │  Stage  │    │ Stage   │    │  Stage  │    │  Stage  │
└─────────┘    └─────────┘    └─────────┘    └─────────┘    └─────────┘
```

Each stage is implemented as a separate SystemVerilog module, and `riscv_core.sv` is responsible for their instantiation and interconnection.

#### 3.1.1. Fetch Stage (`fetch_stage.sv`)
For a detailed architectural description of the Fetch Stage, refer to `docs/architecture/pipeline_stages/FETCH_STAGE_ARCHITECTURE.md`.

#### 3.1.2. Decode Stage (`decode_stage.sv`)
For a detailed architectural description of the Decode Stage, refer to `docs/architecture/pipeline_stages/DECODE_STAGE_ARCHITECTURE.md`.

#### 3.1.3. Execute Stage (`execute_stage.sv`)
For a detailed architectural description of the Execute Stage, refer to `docs/architecture/pipeline_stages/EXECUTE_STAGE_ARCHITECTURE.md`.

#### 3.1.4. Memory Stage (`mem_stage.sv`)
For a detailed architectural description of the Memory Stage, refer to `docs/architecture/pipeline_stages/MEMORY_STAGE_ARCHITECTURE.md`.

#### 3.1.5. Writeback Stage (`writeback_stage.sv`)
For a detailed architectural description of the Writeback Stage, refer to `docs/architecture/pipeline_stages/WRITEBACK_STAGE_ARCHITECTURE.md`.

### 3.1. Pipeline Registers
Data and control signals are passed between stages via dedicated pipeline registers. These registers are typically implemented as `always_ff` blocks within `riscv_core.sv` or within the stage modules themselves, ensuring synchronous data transfer.

### 3.2. Data Path Flow
- **Instruction Flow**: Instructions are fetched by the Fetch stage, passed to Decode, then Execute, Memory, and finally Writeback.
- **Data Flow**: Register operands are read in Decode, processed in Execute, memory accesses occur in Memory, and results are written back to the Register File in Writeback.

### 3.3. Control Path Flow
- **Control Signal Generation**: Control signals are generated primarily in the Decode stage based on the instruction.
- **Control Signal Propagation**: These signals propagate through the pipeline registers, enabling the correct operation of functional units in subsequent stages.
- **Hazard Signals**: Stall and flush signals generated by the hazard unit propagate *backwards* through the pipeline to control fetching and decoding.

## 4. Functional Unit Integration

`riscv_core.sv` also integrates various functional units that support the main pipeline:

- **Hazard Unit**: Monitors pipeline state and generates stall/flush signals to resolve data and control hazards.
- **CSR Register File**: Manages all Machine-mode Control and Status Registers (CSRs), handling reads, writes, and updates during exceptions.
- **Branch Predictor**: Provides predicted branch targets and outcomes to the Fetch stage.
- **Instruction Cache (ICache)**: Provides instructions to the Fetch stage.
- **Data Cache (DCache)**: Handles load/store requests from the Memory stage.
- **FPU/VPU/MLIU**: Integrated into the Execute stage for specialized operations.

## 5. Top-Level Interfaces

`riscv_core.sv` exposes the following top-level interfaces to the external environment:

- **Clock and Reset**: `clk_i`, `rst_ni`
- **Unified Memory Interface**: `mem_if` for communication with the external memory system (L3 cache or memory wrapper).
- **Interrupt Interface**: `m_software_interrupt_i`, `m_timer_interrupt_i`, `m_external_interrupt_i` for handling machine-mode interrupts.
- **Debug Interface**: (Future) For external debugging and control.

## 6. Configuration and Parameterization

`riscv_core.sv` is parameterized to allow flexible configuration of the core, such as enabling/disabling functional units (FPU, VPU), setting cache sizes, and defining reset vectors. These parameters are often passed down to instantiated sub-modules.

## 7. Future Enhancements

- **MMU/TLB Integration**: Integration of the Memory Management Unit for virtual memory support.
- **RVC Instruction Support**: Modifications to handle 16-bit compressed instructions.
- **Advanced Branch Prediction**: Integration of dynamic branch prediction mechanisms.
- **Performance Monitoring**: Enhanced performance counters and analysis capabilities.
- **Debug Interface**: Full implementation of a hardware debug interface.