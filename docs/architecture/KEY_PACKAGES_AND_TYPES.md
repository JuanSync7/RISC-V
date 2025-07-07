# Key Packages and Types

## 1. Overview
This document provides an overview of the key SystemVerilog packages (`.sv` files containing `package ... endpackage` blocks) used in the RISC-V core design. These packages are essential for defining shared data types, constants, enumerations, and functions that are used across multiple modules, promoting consistency, type safety, and code reusability.

## 2. Importance of Packages
- **Global Definitions**: Provide a centralized location for definitions that need to be accessible throughout the design.
- **Type Safety**: Define custom data types (e.g., structs, enums) that improve code readability and help catch errors at compile time.
- **Consistency**: Ensure that all modules use the same definitions for common parameters, opcodes, and control signals.
- **Reusability**: Facilitate the reuse of common logic and data structures across different parts of the design.

## 3. Key Packages in the Design

### 3.1. `riscv_config_pkg.sv`
- **Purpose**: Defines global configuration parameters for the entire RISC-V core. These parameters control major architectural features, sizes, and enable/disable various functional units.
- **Key Contents**:
    - **Core Architecture**: `XLEN`, `ADDR_WIDTH`, `REG_COUNT`, `DEFAULT_RESET_VECTOR`.
    - **Instruction Encoding**: Opcodes (`OPCODE_LUI`, `OPCODE_JAL`, etc.), DPU Funct3/Funct7 fields, `NOP_INSTRUCTION`.
    - **Exception and Interrupt**: `CAUSE_MISALIGNED_FETCH`, `CAUSE_ILLEGAL_INSTRUCTION`, `CAUSE_ECALL_U`, `CAUSE_INTERRUPT`, CSR addresses (`MSTATUS_ADDR`, `MEPC_ADDR`, etc.).
    - **Multi-Core**: `MAX_CORES`, `DEFAULT_NUM_CORES`, `DEFAULT_TOPOLOGY` (for inter-core communication).
    - **Cache System**: `DEFAULT_L1_CACHE_SIZE`, `DEFAULT_L2_CACHE_SIZE`, `DEFAULT_CACHE_LINE_SIZE`, associativity (`DEFAULT_L1_CACHE_WAYS`), replacement policies (`DEFAULT_L1_REPLACEMENT`), coherency protocol (`DEFAULT_COHERENCY_PROTOCOL`).
    - **Branch Predictor**: `DEFAULT_BTB_ENTRIES`, `DEFAULT_BHT_ENTRIES`, `DEFAULT_GLOBAL_HISTORY_WIDTH`, counter widths, `DEFAULT_BRANCH_PREDICTOR_TYPE`.
    - **Out-of-Order Engine**: `DEFAULT_ROB_SIZE`, `DEFAULT_RS_SIZE`, `DEFAULT_PHYS_REGS`, functional unit counts (`DEFAULT_NUM_ALU_UNITS`).
    - **Memory System**: Prefetch unit parameters, AXI4 parameters (`DEFAULT_AXI4_ID_WIDTH`).
    - **Performance**: `TARGET_FREQ_ASIC`, `DEFAULT_PIPELINE_STAGES`, performance counters.
    - **Security and Safety**: `DEFAULT_ECC_WIDTH`, `DEFAULT_PARITY_WIDTH`.
    - **Debug**: `ENABLE_DEBUG_MODULE`, `DEFAULT_DEBUG_ADDRESS_BASE`, `ENABLE_TRACE_UNIT`.
    - **Power Management**: `DEFAULT_POWER_DOMAINS`, `ENABLE_CLOCK_GATING`.
    - **Accelerator**: `ENABLE_FPU`, `ENABLE_VPU`, `ENABLE_ML_INFERENCE`.
    - **FPGA vs ASIC**: `DEFAULT_TARGET`, `FPGA_OPTIMIZATIONS`, `ASIC_PROCESS_NODE`.
    - **Functions**:
        - `validate_cache_config(cache_size, line_size, ways)`: Validates cache configuration parameters.
        - `calc_cache_sets(cache_size, line_size, ways)`: Calculates the number of sets in a cache.
        - `calc_cache_index_bits(cache_size, line_size, ways)`: Calculates the number of index bits for a cache.
        - `calc_cache_offset_bits(line_size)`: Calculates the number of offset bits for a cache line.
        - `calc_cache_tag_bits(addr_width, cache_size, line_size, ways)`: Calculates the number of tag bits for a cache.
- **Usage**: Imported by modules that need to access global configuration settings.

### 3.2. `riscv_core_pkg.sv`
- **Purpose**: Contains core-wide definitions, including common data types, enumerations for control signals, and instruction-related constants.
- **Key Contents**:
    - `addr_t`, `word_t` (typedefs for address and data words)
    - `if_id_reg_t`, `id_ex_reg_t`, etc. (typedefs for pipeline registers)
    - `alu_op_e` (enum for ALU operations)
    - `opcode_e`, `funct3_e`, `funct7_e` (enums for instruction fields)
    - `ctrl_signals_t` (struct for pipeline control signals)
    - `exception_info_t`, `exception_type_e`, `exception_cause_t` (for exception handling)
- **Usage**: Widely imported by pipeline stages and functional units.

### 3.3. `riscv_mem_types_pkg.sv`
- **Purpose**: Defines data types and constants specific to the memory subsystem, including cache-related structures and memory access types.
- **Key Contents**:
    - `cache_state_t`: Enumeration for MESI cache coherency states (Invalid, Shared, Exclusive, Modified).
        ```systemverilog
        typedef enum logic [1:0] {
            I, // Invalid
            S, // Shared
            E, // Exclusive
            M  // Modified
        } cache_state_t;
        ```
    - `coherency_req_type_e`: Enumeration for coherency request types (e.g., `COHERENCY_REQ_READ`, `COHERENCY_REQ_INVALIDATE`).
        ```systemverilog
        typedef enum logic [1:0] {
            COHERENCY_REQ_READ,
            COHERENCY_REQ_WRITE,
            COHERENCY_REQ_INVALIDATE,
            COHERENCY_REQ_UPGRADE
        } coherency_req_type_e;
        ```
    - `memory_req_t`: Structure for memory requests.
        ```systemverilog
        typedef struct packed {
            addr_t                      addr;           // Memory address
            logic                       write;          // 1=write, 0=read
            word_t                      data;           // Write data for the current beat
            logic [3:0]                 strb;           // Write strobes
            logic [3:0]                 id;             // Transaction ID
            logic [CORE_ID_WIDTH-1:0]   source_id;      // ID of the core/master initiating the request
            logic                       coherent;       // Request requires coherency management
            logic [7:0]                 burst_len;      // Number of beats in the burst (for cache lines)
            logic                       burst_last;     // Indicates the last beat of a request burst
            logic                       cacheable;      // Cacheable transaction
            logic [2:0]                 prot;           // Protection level
            logic [2:0]                 size;           // Deprecated in favor of burst, but kept for compatibility
        } memory_req_t;
        ```
    - `memory_rsp_t`: Structure for memory responses.
        ```systemverilog
        typedef struct packed {
            word_t                      data;           // Read data for the current beat
            logic [3:0]                 id;             // Transaction ID
            logic                       error;          // Error flag
            logic                       last;           // Indicates the last beat of a response burst
        } memory_rsp_t;
        ```
- **Usage**: Imported by cache modules, memory controllers, and the memory stage.

### 3.3. `riscv_bp_types_pkg.sv`
- **Purpose**: Contains all shared parameters, data types, and enumerations related to branch prediction.
- **Key Contents**:
    - `btb_entry_t`: Structure for a single Branch Target Buffer entry.
        ```systemverilog
        typedef struct packed {
            logic        valid;      // Valid bit for this entry
            addr_t       tag;        // PC tag for matching
            addr_t       target;     // Branch target address
            logic [BTB_COUNTER_WIDTH-1:0] counter;    // 2-bit saturating counter
            logic        is_branch;  // Indicates if this is a branch instruction
        } btb_entry_t;
        ```
    - `bht_entry_t`: Structure for a single Branch History Table entry.
        ```systemverilog
        typedef struct packed {
            logic [BHT_COUNTER_WIDTH-1:0] counter;    // 2-bit saturating counter
            logic        valid;      // Valid bit
        } bht_entry_t;
        ```
    - `pht_entry_t`: Structure for a single Pattern History Table entry.
    - `selector_entry_t`: Structure for a Tournament Predictor Selector Table entry.
    - `rsb_entry_t`: Structure for a Return Stack Buffer entry.
    - `global_history_t`: Type for the Global History Register.
    - `branch_prediction_t`: Structure for branch prediction results.
        ```systemverilog
        typedef struct packed {
            logic        taken;       // Prediction: taken or not taken
            addr_t       target;      // Predicted target address
            logic        btb_hit;     // BTB hit indicator
            logic        bht_hit;     // BHT hit indicator
            logic        pht_hit;     // PHT hit indicator
            logic        rsb_hit;     // RSB hit indicator
            addr_t       ras_target;  // Predicted return address from RAS
            logic [CONFIDENCE_WIDTH-1:0] confidence; // Prediction confidence
        } branch_prediction_t;
        ```
    - `branch_update_t`: Structure for branch update information from the Execute stage.
        ```systemverilog
        typedef struct packed {
            logic        valid;       // Update is valid
            addr_t       pc;          // Branch PC
            addr_t       target;      // Actual target
            logic        taken;       // Actual outcome
            logic        is_branch;   // Is this a branch instruction
            logic        is_return;   // Is this a return instruction
            logic        is_call;     // Is this a call instruction
            logic        mispredicted; // Was prediction wrong
        } branch_update_t;
        ```
    - `bp_state_e`: Enumeration for Branch Predictor State Machine states.
    - `branch_type_e`: Enumeration for different branch instruction types.
    - `predictor_type_e`: Enumeration for different branch predictor types.
    - `bp_perf_counters_t`: Structure for branch predictor performance counters.
    - `bp_config_t`: Structure for branch predictor configuration.
    - Functions:
        - `calculate_btb_index(pc, btb_entries)`: Calculates the index into the BTB based on the program counter (PC).
        - `calculate_bht_index(pc, global_history, bht_entries)`: Calculates the index into the BHT using PC and global history.
        - `calculate_pht_index(global_history, pht_entries)`: Calculates the index into the PHT using global history.
        - `calculate_selector_index(pc, global_history, selector_entries)`: Calculates the index into the tournament predictor selector table.
        - `classify_branch(instruction)`: Classifies the type of branch instruction (conditional, unconditional, call, return, indirect).
        - `is_branch_instruction(instruction)`: Checks if the given instruction is a branch instruction.
        - `is_return_instruction(instruction)`: Checks if the given instruction is a return instruction.
        - `is_call_instruction(instruction)`: Checks if the given instruction is a call instruction.
- **Usage**: Imported by the Fetch stage and branch predictor modules.

### 3.4. `riscv_cache_topology_pkg.sv`
- **Purpose**: Defines parameters and types related to the cache hierarchy topology, such as the number of cache levels and their interconnections.
- **Key Contents**:
    - `cache_topology_e`: Enumeration for cache topology configurations (e.g., `CACHE_TOPOLOGY_UNIFIED`, `CACHE_TOPOLOGY_CLUSTERED`).
        ```systemverilog
        typedef enum logic [2:0] {
            CACHE_TOPOLOGY_UNIFIED    = 3'b000,  // Single L2 + Single L3 (current)
            CACHE_TOPOLOGY_CLUSTERED  = 3'b001,  // Multiple L2 clusters + Single L3
            CACHE_TOPOLOGY_DISTRIBUTED = 3'b010, // Multiple L2 + Multiple L3
            CACHE_TOPOLOGY_NUMA       = 3'b011,  // NUMA-aware cache distribution
            CACHE_TOPOLOGY_HIERARCHICAL = 3'b100, // Multi-level cache clusters
            CACHE_TOPOLOGY_CUSTOM     = 3'b111   // User-defined topology
        } cache_topology_e;
        ```
    - `cache_cluster_config_t`: Structure for cache cluster configuration.
        ```systemverilog
        typedef struct packed {
            logic [3:0]             cluster_id;           // Unique cluster ID
            logic [3:0]             num_cores;            // Cores in this cluster
            logic [7:0]             core_mask;            // Which cores belong to cluster
            logic [31:0]            l2_cache_size;        // L2 cache size for cluster
            logic [3:0]             l2_cache_ways;        // L2 associativity
            logic [3:0]             l3_instance_id;       // Which L3 this cluster uses
            logic                   has_local_l3;         // Does cluster have local L3?
            logic [1:0]             memory_controller_id; // Which memory controller
            logic [7:0]             bandwidth_allocation; // Bandwidth percentage
            logic                   coherency_domain;     // Coherency domain membership
        } cache_cluster_config_t;
        ```
    - `system_cache_topology_t`: Structure for system-wide cache topology configuration.
    - `l2_instance_config_t`, `l3_instance_config_t`: Structures for L2/L3 cache instance configurations.
    - `cache_interconnect_e`: Enumeration for cache interconnect types (e.g., `INTERCONNECT_BUS`, `INTERCONNECT_CROSSBAR`).
    - Functions:
        - `get_unified_topology(num_cores, l2_size, l3_size)`: Returns a `system_cache_topology_t` for a unified cache topology.
        - `get_clustered_topology(num_cores, l2_size, l3_size)`: Returns a `system_cache_topology_t` for a clustered cache topology.
        - `get_numa_topology(num_cores, l2_size, l3_size)`: Returns a `system_cache_topology_t` for a NUMA-aware cache topology.
        - `get_l2_instance_for_address(address, topology)`: Determines which L2 cache instance should handle a given address.
        - `get_l3_instance_for_address(address, topology)`: Determines which L3 cache instance should handle a given address.
        - `get_l2_for_core(core_id, topology)`: Returns the L2 cache instance ID associated with a given core ID.
        - `validate_cache_topology(topology, total_cores)`: Validates the provided cache topology configuration.
- **Usage**: Imported by modules involved in cache integration and coherency.

### 3.6. `riscv_cache_types_pkg.sv`
- **Purpose**: Defines common data types and structures used across various cache modules.
- **Key Contents**:
    - `cache_line_t`: Structure for a cache line, including `valid`, `tag`, `data`, `dirty`, `lru` bits.
        ```systemverilog
        typedef struct packed {
            logic                    valid;      // Valid bit
            logic [TAG_BITS-1:0]     tag;        // Tag bits (calculated per cache)
            word_t                   data [DEFAULT_CACHE_LINE_SIZE/4-1:0];  // Data array
            logic                    dirty;      // Dirty bit for write-back
            logic                    lru;        // LRU bit (for 2-way cache)
        } cache_line_t;
        ```
    - `cache_state_e`: Enumeration for cache state machine states (e.g., `CACHE_IDLE`, `CACHE_LOOKUP`, `CACHE_HIT`, `CACHE_MISS`).
        ```systemverilog
        typedef enum logic [2:0] {
            CACHE_IDLE,           // Ready for new requests
            CACHE_LOOKUP,         // Performing cache lookup
            CACHE_HIT,            // Cache hit, returning data
            CACHE_MISS,           // Cache miss, initiating fill
            CACHE_FILL,           // Filling cache line from memory
            CACHE_WRITEBACK,      // Writing back dirty line
            CACHE_FLUSH           // Flushing cache
        } cache_state_e;
        ```
    - `cache_req_t`: Structure for cache requests.
        ```systemverilog
        typedef struct packed {
            logic        valid;
            addr_t       addr;
            logic [2:0]  size;
            logic        write;
            word_t       data;
            logic [3:0]  strb;
            logic [3:0]  id;
        } cache_req_t;
        ```
    - `cache_rsp_t`: Structure for cache responses.
        ```systemverilog
        typedef struct packed {
            logic        valid;
            word_t       data;
            logic        hit;
            logic        error;
            logic [3:0]  id;
        } cache_rsp_t;
        ```
    - `cache_stats_t`: Structure for cache statistics.
    - `cache_config_t`: Structure for cache configuration parameters.
    - `cache_addr_t`: Structure for decomposed cache address (tag, index, offset).
    - `replacement_policy_e`, `write_policy_e`, `allocation_policy_e`: Enumerations for cache policies.
    - `cache_coherency_state_e`: Enumeration for MESI cache coherency states.
    - `snoop_op_e`: Enumeration for cache snoop operations.
    - `cache_perf_counters_t`: Structure for cache performance counters.
    - Functions:
        - `create_cache_config(size, ways, line_size)`: Creates a `cache_config_t` structure based on provided parameters.
        - `decompose_cache_addr(addr, config)`: Decomposes a given address into tag, index, and offset based on cache configuration.
        - `is_cache_aligned(addr, line_size)`: Checks if an address is aligned to a cache line boundary.
        - `get_cache_line_words(line_size)`: Returns the number of words (32-bit) in a cache line, assuming 4 bytes per word.
- **Usage**: Imported by all cache modules (I-Cache, D-Cache, L2, L3).

### 3.7. `riscv_dpu_types_pkg.sv`
- **Purpose**: Defines data types and constants specific to the Data Processing Units (DPUs), including FPU, VPU, and MLIU.
- **Key Contents**:
    - `dpu_req_t`: Structure for DPU requests.
        ```systemverilog
        typedef struct packed {
            logic        valid;
            logic [6:0]  opcode; // DPU operation code
            word_t       data;   // Input data
            addr_t       addr;   // Address for memory-mapped operations
        } dpu_req_t;
        ```
    - `dpu_rsp_t`: Structure for DPU responses.
        ```systemverilog
        typedef struct packed {
            logic        valid;
            word_t       data;   // Output data
            logic        error;  // Error indicator
        } dpu_rsp_t;
        ```
- **Usage**: Imported by the decode stage and DPU functional units.

### 3.8. `riscv_exception_pkg.sv`
- **Purpose**: Defines enumerations and structures for exception and interrupt handling.
- **Key Contents**:
    - `exception_info_t`: Structure to hold information about an exception or interrupt.
        ```systemverilog
        typedef struct packed {
            logic        valid;
            logic [31:0] cause;
            addr_t       pc;
            word_t       tval;
            logic        interrupt;
            logic        exception;
        } exception_info_t;
        ```
    - `interrupt_vector_t`: Structure representing pending interrupts.
        ```systemverilog
        typedef struct packed {
            logic        software_int;
            logic        timer_int;
            logic        external_int;
            logic [15:0] reserved;
        } interrupt_vector_t;
        ```
    - CSR Register Structures: `mstatus_t`, `mtvec_t`, `mie_t`, `mip_t` for Machine Status, Trap Vector, Machine Interrupt Enable, and Machine Interrupt Pending registers, respectively.
    - `exception_priority_e`: Enumeration for different exception priority levels.
    - `exception_state_e`: Enumeration for states of the exception handler state machine.
    - Functions:
        - `is_valid_exception_cause(cause)`: Checks if a given cause code corresponds to a valid exception.
        - `is_valid_interrupt_cause(cause)`: Checks if a given cause code corresponds to a valid interrupt.
        - `get_exception_priority(cause)`: Returns the priority level for a given exception or interrupt cause.
- **Usage**: Imported by pipeline stages for exception detection and the exception handler module.

### 3.9. `riscv_fpu_types_pkg.sv`
- **Purpose**: Defines data types and structures for the Floating Point Unit (FPU) interface.
- **Key Contents**:
    - `fpu_op_e`: Enumeration for FPU operation codes (e.g., `FPU_ADD`, `FPU_MUL`, `FPU_SQRT`).
        ```systemverilog
        typedef enum logic [3:0] {
            FPU_ADD,    // Floating-point add
            FPU_SUB,    // Floating-point subtract
            FPU_MUL,    // Floating-point multiply
            FPU_DIV,    // Floating-point divide
            FPU_SQRT,   // Floating-point square root
            FPU_F2I,    // Float to Integer conversion
            FPU_I2F,    // Integer to Float conversion
            FPU_FMA     // Fused Multiply-Add (A * B + C)
        } fpu_op_e;
        ```
    - `fpu_req_t`: Structure for FPU requests, including opcode and operands.
        ```systemverilog
        typedef struct packed {
            logic        valid;
            fpu_op_e     opcode;
            word_t       operand1;
            word_t       operand2;
            word_t       operand3; // Added for FMA operation
            logic [4:0]  rd_addr; // Destination register address
            logic [4:0]  rs1_addr; // Source register 1 address
            logic [4:0]  rs2_addr; // Source register 2 address
        } fpu_req_t;
        ```
    - `fpu_rsp_t`: Structure for FPU responses, including result data and error indicator.
        ```systemverilog
        typedef struct packed {
            logic        valid;
            word_t       data;
            logic        error;
            logic [4:0]  rd_addr; // Destination register address
        } fpu_rsp_t;
        ```
- **Usage**: Imported by the FPU unit and relevant pipeline stages.

### 3.10. `riscv_ml_types_pkg.sv`
- **Purpose**: Defines data types and structures for the Machine Learning Inference Unit (MLIU) interface.
- **Key Contents**:
    - `mliu_op_e`: Enumeration for MLIU operation codes (e.g., `MLIU_MATRIX_MUL`, `MLIU_CONVOLUTION`, `MLIU_RELU`).
        ```systemverilog
        typedef enum logic [3:0] {
            MLIU_MATRIX_MUL,    // Matrix Multiplication
            MLIU_CONVOLUTION,   // Convolutional Layer
            MLIU_ACTIVATION,    // Activation Function
            MLIU_POOLING,
            MLIU_RELU,          // Rectified Linear Unit activation
            MLIU_SIGMOID,       // Sigmoid activation
            MLIU_TANH,          // Tanh activation
            MLIU_MAX_POOL,      // Max Pooling
            MLIU_AVG_POOL       // Average Pooling
        } mliu_op_e;
        ```
    - `mliu_req_t`: Structure for MLIU requests, including opcode and operands.
        ```systemverilog
        typedef struct packed {
            logic        valid;
            mliu_op_e    opcode;
            word_t       operand1; // Input data / pointer
            word_t       operand2; // Weights / kernel / pointer
            logic [4:0]  rd_addr;    // Destination register address
        } mliu_req_t;
        ```
    - `mliu_rsp_t`: Structure for MLIU responses, including result data and error indicator.
        ```systemverilog
        typedef struct packed {
            logic        valid;
            word_t       data;
            logic        error;
            logic [4:0]  rd_addr; // Destination register address
        } mliu_rsp_t;
        ```
- **Usage**: Imported by the MLIU unit and relevant pipeline stages.

### 3.12. `riscv_ooo_types_pkg.sv`
- **Purpose**: Contains all shared parameters, data types, and enumerations related to the out-of-order execution engine.
- **Key Contents**:
    - `rob_tag_t`, `rs_tag_t`, `phys_reg_addr_t`, `arch_reg_addr_t`: Type definitions for various out-of-order identifiers.
    - `rob_entry_t`: Structure for a Reorder Buffer entry.
        ```systemverilog
        typedef struct packed {
            logic        valid;          // Entry is valid
            logic        ready;          // Result is ready
            logic        exception;      // Exception occurred
            logic [31:0] exception_cause; // Exception cause
            addr_t       pc;             // Program counter
            word_t       result;         // Execution result
            arch_reg_addr_t rd_addr;     // Destination register
            logic        reg_write;      // Write to register file
            logic        mem_read;       // Memory read operation
            logic        mem_write;      // Memory write operation
            logic        branch;         // Branch instruction
            logic        jump;           // Jump instruction
            logic        csr_read;       // CSR read operation
            logic        csr_write;      // CSR write operation
            logic [11:0] csr_addr;       // CSR address
        } rob_entry_t;
        ```
    - `rs_entry_t`: Structure for a Reservation Station entry.
        ```systemverilog
        typedef struct packed {
            logic        busy;           // Entry is busy
            logic        valid;          // Entry is valid
            word_t       instruction;    // Instruction
            addr_t       pc;             // Program counter
            rob_tag_t    rob_tag;        // ROB tag
            arch_reg_addr_t rd_addr;     // Destination register
            word_t       rs1_data;       // RS1 data (if ready)
            word_t       rs2_data;       // RS2 data (if ready)
            logic        rs1_ready;      // RS1 is ready
            logic        rs2_ready;      // RS2 is ready
            rob_tag_t    rs1_tag;        // RS1 ROB tag (if not ready)
            rob_tag_t    rs2_tag;        // RS2 ROB tag (if not ready)
            logic        mem_read;       // Memory read operation
            logic        mem_write;      // Memory write operation
            logic        branch;         // Branch instruction
            logic        jump;           // Jump instruction
            logic        csr_read;       // CSR read operation
            logic        csr_write;      // CSR write operation
            logic [11:0] csr_addr;       // CSR address
        } rs_entry_t;
        ```
    - `cdb_entry_t`: Structure for a Common Data Bus entry.
    - `rename_table_entry_t`: Structure for a Register Renaming Table entry.
    - `fu_type_e`: Enumeration for Functional Unit types (e.g., `FU_ALU`, `FU_MULT`, `FU_DIV`, `FU_MEM`).
    - `issue_state_e`: Enumeration for instruction issue states.
    - `ooo_perf_counters_t`: Structure for out-of-order performance counters.
    - `ooo_config_t`: Structure for out-of-order configuration parameters.
    - `ooo_state_e`: Enumeration for out-of-order state machine states.
    - Functions:
        - `is_alu_instruction(instruction)`: Checks if an instruction is an ALU operation.
        - `is_mult_instruction(instruction)`: Checks if an instruction is a multiply operation.
        - `is_div_instruction(instruction)`: Checks if an instruction is a divide operation.
        - `is_memory_instruction(instruction)`: Checks if an instruction is a memory operation.
        - `get_fu_type(instruction)`: Returns the functional unit type for a given instruction.
        - `get_fu_latency(fu_type)`: Returns the latency of a functional unit.
- **Usage**: Imported by the out-of-order engine modules (Reorder Buffer, Reservation Stations, etc.).

### 3.13. `riscv_protocol_constants_pkg.sv`
- **Purpose**: Centralized package containing all protocol-specific constants, opcodes, and configuration values used throughout the RISC-V system. Eliminates hardcoded values and provides single source of truth for protocol specs.
- **Key Contents**:
    - **AXI4 Protocol Constants**: Burst types (`AXI4_BURST_FIXED`, `AXI4_BURST_INCR`), response codes (`AXI4_RESP_OKAY`, `AXI4_RESP_SLVERR`), cache attributes (`AXI4_CACHE_DEVICE_NON_BUFFERABLE`), protection attributes (`AXI4_PROT_PRIVILEGED_SECURE_DATA`), size encoding (`AXI4_SIZE_4_BYTES`), and default values.
    - **CHI Protocol Constants**: Request opcodes (`CHI_REQ_ReadNoSnp`, `CHI_REQ_WriteUniqueFullStash`), response opcodes (`CHI_RSP_CompData`, `CHI_RSP_SnpRespData`), data opcodes (`CHI_DAT_DataLCrdReturn`), size encoding, response error codes, memory attributes, and order encoding.
    - **TileLink Protocol Constants**: A-Channel opcodes (`TL_A_PutFullData`, `TL_A_Get`), D-Channel opcodes (`TL_D_AccessAck`, `TL_D_GrantData`), size encoding, arithmetic operations (`TL_ARITH_ADD`), logical operations (`TL_LOGICAL_XOR`), and parameters.
    - **Cache Coherency Constants**: MESI cache states (`CACHE_STATE_INVALID`, `CACHE_STATE_MODIFIED`), extended cache line states (`CACHE_LINE_SHARED`, `CACHE_LINE_OWNED`), and cache request types (`CACHE_REQ_READ`, `CACHE_REQ_INVALIDATE`).
    - **Performance and Timing Constants**: Default timeout values (`TIMEOUT_AXI4_TRANSACTION`, `TIMEOUT_CACHE_MISS`), performance counter defaults, and queue/buffer sizes.
    - **Debug and Verification Constants**: Debug operation codes (`DEBUG_OP_HALT`, `DEBUG_OP_READ_REG`), verification stimulus constants (`VERIF_MAGIC_START`, `VERIF_MAGIC_PASS`), and test address ranges.
    - **Memory System Constants**: Memory request priorities, memory access types, and common address constants.
    - **Reset and Initialization Constants**: Reset values and initialization patterns.
- **Usage**: Imported by modules that interact with various protocols or require system-wide constants.

### 3.14. `riscv_protocol_types_pkg.sv`
- **Purpose**: Contains all shared parameters, data types, and enumerations related to memory protocol adapters (AXI4, CHI, TileLink, etc.). This includes protocol-specific structures and state machines.
- **Key Contents**:
    - Protocol Configuration Parameters: `AXI4_ID_WIDTH`, `AXI4_ADDR_WIDTH`, `AXI4_DATA_WIDTH`, `AXI4_STRB_WIDTH`.
    - `protocol_type_e`: Enumeration for different protocol types (e.g., `PROTOCOL_AXI4`, `PROTOCOL_CHI`, `PROTOCOL_TILELINK`).
    - `axi4_state_e`: Enumeration for AXI4 state machine states.
    - `axi4_transaction_t`: Structure for AXI4 transaction tracking.
    - `protocol_perf_counters_t`: Structure for protocol performance counters.
    - `protocol_error_e`: Enumeration for protocol error types.
    - `burst_type_e`: Enumeration for burst types (e.g., `BURST_FIXED`, `BURST_INCR`, `BURST_WRAP`).
    - `cache_attributes_t`: Structure for cache attributes.
    - Functions:
        - `convert_to_axi4_addr(mem_addr)`: Converts a memory address to an AXI4 address.
        - `convert_to_axi4_size(mem_size)`: Converts a memory size to an AXI4 size encoding.
        - `convert_to_axi4_strb(mem_strb)`: Converts a memory strobe to an AXI4 strobe.
- **Usage**: Imported by protocol adapter modules and memory interfaces.

### 3.15. `riscv_qos_pkg.sv`
- **Purpose**: Comprehensive Quality of Service (QoS) package for RISC-V multi-core system. Defines QoS levels, arbitration policies, bandwidth allocation, and latency guarantees for optimal system performance.
- **Key Contents**:
    - QoS Level Definitions: `QOS_LEVEL_CRITICAL`, `QOS_LEVEL_HIGH`, `QOS_LEVEL_BEST_EFFORT`, etc.
    - `qos_transaction_type_e`: Enumeration for QoS transaction types (e.g., `QOS_TYPE_DEBUG`, `QOS_TYPE_INSTR_FETCH`, `QOS_TYPE_DMA`).
        ```systemverilog
        typedef enum logic [3:0] {
            QOS_TYPE_DEBUG          = 4'h0,  // Debug access - highest priority
            QOS_TYPE_EXCEPTION      = 4'h1,  // Exception handling - critical
            QOS_TYPE_INSTR_FETCH    = 4'h2,  // Instruction fetch - high priority
            QOS_TYPE_DATA_ACCESS    = 4'h3,  // Data access - medium-high priority  
            QOS_TYPE_CACHE_FILL     = 4'h4,  // Cache line fill - medium priority
            QOS_TYPE_CACHE_WB       = 4'h5,  // Cache writeback - medium-low priority
            QOS_TYPE_PREFETCH       = 4'h6,  // Prefetch operations - low priority
            QOS_TYPE_DMA            = 4'h7,  // DMA transfers - best effort
            QOS_TYPE_PERIPHERAL     = 4'h8,  // Peripheral access - best effort
            QOS_TYPE_MAINTENANCE    = 4'h9,  // Cache maintenance - low priority
            QOS_TYPE_BACKGROUND     = 4'hA,  // Background tasks - best effort
            QOS_TYPE_TEST           = 4'hB,  // Test/verification - configurable
            QOS_TYPE_RESERVED_C     = 4'hC,  // Reserved for future use
            QOS_TYPE_RESERVED_D     = 4'hD,  // Reserved for future use
            QOS_TYPE_RESERVED_E     = 4'hE,  // Reserved for future use
            QOS_TYPE_USER_DEFINED   = 4'hF   // User-defined QoS type
        } qos_transaction_type_e;
        ```
    - `qos_arbiter_policy_e`: Enumeration for QoS arbitration policies (e.g., `QOS_ARBITER_ROUND_ROBIN`, `QOS_ARBITER_STRICT_PRIO`, `QOS_ARBITER_ADAPTIVE`).
    - `qos_config_t`: Structure for QoS configuration, including priority level, transaction type, and bandwidth allocation.
    - `qos_performance_t`: Structure for QoS performance monitoring counters.
    - `qos_request_t`: Structure for QoS transaction requests.
    - `qos_arbiter_state_t`: Structure for QoS arbiter state.
    - `qos_control_reg_t`: Structure for QoS control register.
    - QoS Configuration Parameters: `QOS_ENABLE_DEFAULT`, `QOS_DEFAULT_POLICY`, `QOS_MAX_LEVELS`, arbitration weights (`QOS_WEIGHT_CRITICAL`).
    - Functions:
        - `get_qos_level(txn_type)`: Returns the default QoS level for a given transaction type.
        - `get_default_qos_level(txn_type)`: Returns the default QoS level for a given transaction type.
        - `get_default_bandwidth_percent(qos_level)`: Returns the default bandwidth allocation percentage for a given QoS level.
        - `get_default_max_latency(qos_level)`: Returns the default maximum latency for a given QoS level.
        - `is_real_time_qos(qos_level)`: Checks if a QoS level is considered real-time.
        - `is_preemptable_qos(qos_level)`: Checks if a QoS level allows preemption.
        - `get_qos_weight(qos_level)`: Returns the arbitration weight for a given QoS level.
        - `calculate_priority_score(qos_level, wait_time, weight, urgent)`: Calculates a priority score for arbitration based on QoS level, wait time, weight, and urgency.
- **Usage**: Imported by modules that require QoS management, such as interconnects, memory controllers, and shared resources.

### 3.16. `riscv_types_pkg.sv`
- **Purpose**: Contains fundamental data types, enumerations, and structures that define the core RISC-V architecture and its in-order pipeline.
- **Key Contents**:
    - Base Data Types: `word_t` (for data words), `addr_t` (for addresses), `reg_addr_t` (for register addresses).
    - Control Signal Enumerations: `alu_op_e` (ALU operations), `alu_src_a_sel_e`, `alu_src_b_sel_e` (ALU operand selection), `wb_mux_sel_e` (write-back multiplexer selection).
    - `ctrl_signals_t`: Structure for pipeline control signals.
        ```systemverilog
        typedef struct packed {
            alu_op_e        alu_op;
            alu_src_a_sel_e alu_src_a_sel;
            alu_src_b_sel_e alu_src_b_sel;
            logic           mem_read_en;
            logic           mem_write_en;
            logic           reg_write_en;
            wb_mux_sel_e    wb_mux_sel;
            logic           is_branch;
            logic           mult_en;
            logic           div_en;
            logic           csr_cmd_en;
            logic [2:0]     funct3;
            logic           dpu_en;         // Enable DPU operation
            logic [1:0]     dpu_unit_sel;   // 0: FPU, 1: VPU, 2: MLIU
            logic [6:0]     dpu_op_sel;     // Specific operation within the DPU unit (funct7)
            logic           illegal_instr;  // Illegal instruction flag
        } ctrl_signals_t;
        ```
    - Pipeline Stage Data Structures: `decode_data_t`, `id_ex_reg_t`, `execute_data_t`, `memory_data_t`, `writeback_data_t` for data transfer between pipeline stages.
        ```systemverilog
        typedef struct packed {
            logic        valid;
            addr_t       pc;
            word_t       instruction;
            logic [4:0]  rs1_addr;
            logic [4:0]  rs2_addr;
            logic [4:0]  rd_addr;
            word_t       rs1_data;
            word_t       rs2_data;
            word_t       immediate;
            alu_op_e     alu_op;
            alu_src_a_sel_e alu_src_a_sel;
            alu_src_b_sel_e alu_src_b_sel;
            wb_mux_sel_e wb_sel;
            logic        mem_read;
            logic        mem_write;
            logic [2:0]  mem_size;
            logic [3:0]  mem_strb;
            logic        branch;
            logic        jump;
            logic        csr_read;
            logic        csr_write;
            logic [11:0] csr_addr;
            logic        is_jal;
            addr_t       jal_target;
            logic        is_jalr;
        } decode_data_t;

        typedef struct packed {
            logic        valid;
            addr_t       pc;
            word_t       rs1_data;
            word_t       rs2_data;
            word_t       immediate;
            logic [4:0]  rd_addr;
            ctrl_signals_t ctrl;
            logic [4:0]  rs1_addr; // For hazard unit
            logic [4:0]  rs2_addr; // For hazard unit
            logic        is_jal;
            addr_t       jal_target;
            logic        is_jalr;
            // DPU specific fields
            word_t       fpu_operand_a; // FPU operand A
            word_t       fpu_operand_b; // FPU operand B
            word_t       vpu_operand_a; // VPU operand A
            word_t       vpu_operand_b; // VPU operand B
            word_t       mliu_operand_a; // MLIU operand A
            word_t       mliu_operand_b; // MLIU operand B
        } id_ex_reg_t;

        typedef struct packed {
            logic        valid;
            addr_t       pc;
            word_t       alu_result;
            word_t       rs2_data;
            logic [4:0]  rd_addr;
            wb_mux_sel_e wb_sel;
            logic        mem_read;
            logic        mem_write;
            logic [2:0]  mem_size;
            logic [3:0]  mem_strb;
            logic        branch;
            logic        jump;
            logic        csr_read;
            logic        csr_write;
            logic [11:0] csr_addr;
        } execute_data_t;

        typedef struct packed {
            logic        valid;
            addr_t       pc;
            word_t       mem_data;
            word_t       alu_result;
            logic [4:0]  rd_addr;
            wb_mux_sel_e wb_sel;
            logic        csr_read;
            logic        csr_write;
            logic [11:0] csr_addr;
        } memory_data_t;

        typedef struct packed {
            logic        valid;
            addr_t       pc;
            word_t       result;
            logic [4:0]  rd_addr;
            logic        csr_read;
            logic        csr_write;
            logic [11:0] csr_addr;
        } writeback_data_t;
        ```
    - `hazard_info_t`: Structure for hazard detection information.
        ```systemverilog
        typedef struct packed {
            logic        data_hazard;
            logic        control_hazard;
            logic        structural_hazard;
            logic [4:0]  rs1_addr;
            logic [4:0]  rs2_addr;
            logic [4:0]  rd_addr;
        } hazard_info_t;
        ```
    - `forwarding_info_t`: Structure for forwarding information.
        ```systemverilog
        typedef struct packed {
            logic        rs1_forward;
            logic        rs2_forward;
            logic [1:0]  rs1_forward_stage;
            logic [1:0]  rs2_forward_stage;
            word_t       rs1_forward_data;
            word_t       rs2_forward_data;
        } forwarding_info_t;
        ```
    - `branch_prediction_t`: Structure for branch prediction results (note: this is also defined in `riscv_bp_types_pkg.sv` and should be consolidated).
        ```systemverilog
        typedef struct packed {
            logic        predict_taken;
            addr_t       predict_target;
            logic        btb_hit;
        } branch_prediction_t;
        ```
    - `branch_update_t`: Structure for branch update information (note: this is also defined in `riscv_bp_types_pkg.sv` and should be consolidated).
        ```systemverilog
        typedef struct packed {
            logic        update_valid;
            addr_t       update_pc;
            logic        actual_taken;
            addr_t       actual_target;
            logic        is_branch;
            logic        is_jal;
            addr_t       jal_target;
            logic        is_jalr;
        } branch_update_t;
        ```
    - `instruction_fields_t` (`riscv_instr_t`): Structure for decoded instruction fields.
        ```systemverilog
        typedef struct packed {
            logic [6:0]  opcode;
            logic [2:0]  funct3;
            logic [6:0]  funct7;
            logic [4:0]  rs1;
            logic [4:0]  rs2;
            logic [4:0]  rd;
            logic [11:0] immediate;
        } instruction_fields_t;
        ```
    - `perf_counters_t`: Structure for performance counters.
        ```systemverilog
        typedef struct packed {
            logic [31:0] cycles;
            logic [31:0] instructions;
            logic [31:0] branches;
            logic [31:0] branch_mispredicts;
            logic [31:0] cache_misses;
            logic [31:0] cache_hits;
            logic [31:0] stalls;
        } perf_counters_t;
        ```
- **Usage**: Widely imported by pipeline stages and functional units.

### 3.17. `riscv_verif_types_pkg.sv`
- **Purpose**: Contains all shared parameters, data types, and enumerations related to verification and testing.
- **Key Contents**:
    - Test Configuration Parameters: `VERIF_CLK_PERIOD`, `VERIF_TIMEOUT_CYCLES`, `VERIF_MAX_TEST_ITERATIONS`.
    - `test_result_e`: Enumeration for test results (e.g., `TEST_PASS`, `TEST_FAIL`, `TEST_TIMEOUT`).
        ```systemverilog
        typedef enum logic [1:0] {
            TEST_PASS = 2'b00,
            TEST_FAIL = 2'b01,
            TEST_TIMEOUT = 2'b10,
            TEST_SKIP = 2'b11
        } test_result_e;
        ```
    - `test_stats_t`: Structure for test statistics.
        ```systemverilog
        typedef struct packed {
            integer total_tests;
            integer passed_tests;
            integer failed_tests;
            integer timeout_tests;
            integer skipped_tests;
            real pass_rate;
            integer total_cycles;
            real simulation_time;
        } test_stats_t;
        ```
    - `test_category_e`: Enumeration for test categories (e.g., `FUNCTIONAL_TEST`, `STRESS_TEST`, `REGRESSION_TEST`).
        ```systemverilog
        typedef enum {
            FUNCTIONAL_TEST,
            PERFORMANCE_TEST,
            STRESS_TEST,
            CORNER_CASE_TEST,
            REGRESSION_TEST,
            INTEGRATION_TEST,
            SYSTEM_TEST
        } test_category_e;
        ```
    - `test_priority_e`: Enumeration for test priority levels.
        ```systemverilog
        typedef enum {
            CRITICAL,
            HIGH,
            MEDIUM,
            LOW
        } test_priority_e;
        ```
    - Transaction Types: `alu_transaction_t` (for ALU operations), `memory_transaction_t` (for memory operations).
        ```systemverilog
        typedef struct packed {
            logic [31:0] operand_a;
            logic [31:0] operand_b;
            logic [3:0] operation;
            logic [31:0] result;
            logic zero_flag;
            logic overflow_flag;
            time timestamp;
        } alu_transaction_t;

        typedef struct packed {
            logic [31:0] address;
            logic [31:0] write_data;
            logic [31:0] read_data;
            logic [2:0] size;
            logic [3:0] strb;
            logic read_write;
            logic valid;
            time timestamp;
        } memory_transaction_t;
        ```
    - Verification Functions:
        - `random_word()`: Generates a random 32-bit word.
        - `random_addr()`: Generates a random 32-bit address.
        - `random_reg_addr()`: Generates a random 5-bit register address.
- **Usage**: Imported by testbenches, verification components, and test sequences.

## 4. Usage Guidelines
- **Import Specific Items**: Prefer `import my_pkg::my_type;` over `import my_pkg::*;` to avoid name clashes, unless importing a large number of items.
- **Avoid Circular Dependencies**: Ensure packages do not have circular dependencies on each other.
- **New Definitions**: Add new global definitions to the most appropriate existing package. If a new, distinct functional area emerges, consider creating a new package.

## 5. Future Enhancements
- **Automated Package Documentation**: Generate documentation directly from package contents.
- **Package Dependency Graph**: Visualize package dependencies to identify potential issues.
