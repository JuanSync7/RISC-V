# Memory System Architecture

## Overview

The RISC-V core implements a memory system designed for high performance and flexibility. This document describes the memory hierarchy, interface protocols, and access patterns that enable efficient instruction and data access.

## Memory Hierarchy

### Memory Organization
```
┌─────────────────────────────────────────────────────────────┐
│                    RISC-V Core                              │
├─────────────────────────────────────────────────────────────┤
│  Instruction Fetch  │  Data Access                          │
│  (AXI4-Lite Read)   │  (AXI4-Lite Read/Write)               │
├─────────────────────────────────────────────────────────────┤
│                    AXI4-Lite Interface                      │
├─────────────────────────────────────────────────────────────┤
│  Instruction Memory │  Data Memory  │  Peripheral Memory    │
│  (ROM/Flash)        │  (RAM)        │  (UART, Timer, etc.)  │
└─────────────────────────────────────────────────────────────┘
```

### Memory Map
```
Address Range          | Size      | Description
───────────────────────|───────────|──────────────────────────
0x0000_0000 - 0x1FFF_FFFF | 512MB   | Instruction Memory
0x2000_0000 - 0x3FFF_FFFF | 512MB   | Data Memory
0x4000_0000 - 0x4FFF_FFFF | 256MB   | Peripheral Memory
0x5000_0000 - 0x5FFF_FFFF | 256MB   | Reserved
0x6000_0000 - 0x7FFF_FFFF | 512MB   | External Memory
0x8000_0000 - 0xFFFF_FFFF | 2GB     | Reserved
```

## AXI4-Lite Interface

### Interface Overview
The core uses AXI4-Lite protocol for memory access, providing a simple, efficient interface suitable for embedded systems.

### Interface Signals

#### Read Address Channel
```systemverilog
// Instruction Memory Interface
input  logic        i_arready_i,  // Read address ready
output logic        i_arvalid_o,  // Read address valid
output addr_t       i_araddr_o,   // Read address
output logic [2:0]  i_arprot_o,   // Protection type

// Data Memory Interface
input  logic        d_arready_i,  // Read address ready
output logic        d_arvalid_o,  // Read address valid
output addr_t       d_araddr_o,   // Read address
output logic [2:0]  d_arprot_o,   // Protection type
```

#### Read Data Channel
```systemverilog
// Instruction Memory Interface
input  word_t       i_rdata_i,    // Read data
input  logic        i_rvalid_i,   // Read data valid
output logic        i_rready_o,   // Read data ready
input  logic [1:0]  i_rresp_i,    // Read response

// Data Memory Interface
input  word_t       d_rdata_i,    // Read data
input  logic        d_rvalid_i,   // Read data valid
output logic        d_rready_o,   // Read data ready
input  logic [1:0]  d_rresp_i,    // Read response
```

#### Write Address Channel
```systemverilog
// Data Memory Interface (Write Only)
input  logic        d_awready_i,  // Write address ready
output logic        d_awvalid_o,  // Write address valid
output addr_t       d_awaddr_o,   // Write address
output logic [2:0]  d_awprot_o,   // Protection type
```

#### Write Data Channel
```systemverilog
// Data Memory Interface
input  logic        d_wready_i,   // Write data ready
output logic        d_wvalid_o,   // Write data valid
output word_t       d_wdata_o,    // Write data
output logic [3:0]  d_wstrb_o,    // Write strobes
```

#### Write Response Channel
```systemverilog
// Data Memory Interface
input  logic [1:0]  d_bresp_i,    // Write response
input  logic        d_bvalid_i,   // Write response valid
output logic        d_bready_o,   // Write response ready
```

### Protocol Compliance

#### Read Transaction
```systemverilog
// Read transaction sequence
always @(posedge clk_i) begin
    if (rst_ni) begin
        // 1. Assert address and valid
        if (read_request) begin
            i_araddr_o <= pc_f_o;
            i_arvalid_o <= 1'b1;
        end
        
        // 2. Wait for ready
        if (i_arvalid_o && i_arready_i) begin
            i_arvalid_o <= 1'b0;
        end
        
        // 3. Accept data
        if (i_rvalid_i && i_rready_o) begin
            instruction <= i_rdata_i;
        end
    end
end
```

#### Write Transaction
```systemverilog
// Write transaction sequence
always @(posedge clk_i) begin
    if (rst_ni) begin
        // 1. Assert write address
        if (store_request) begin
            d_awaddr_o <= mem_addr;
            d_awvalid_o <= 1'b1;
        end
        
        // 2. Assert write data
        if (d_awvalid_o && d_awready_i) begin
            d_wdata_o <= store_data;
            d_wstrb_o <= byte_enable;
            d_wvalid_o <= 1'b1;
            d_awvalid_o <= 1'b0;
        end
        
        // 3. Complete transaction
        if (d_wvalid_o && d_wready_i) begin
            d_wvalid_o <= 1'b0;
        end
    end
end
```

## Memory Access Patterns

### Instruction Fetch

#### Sequential Access
```systemverilog
// Sequential instruction fetch
always @(posedge clk_i) begin
    if (rst_ni && !stall_f) begin
        if (branch_taken) begin
            pc_f_o <= branch_target;
        end else begin
            pc_f_o <= pc_f_o + 4;  // Sequential access
        end
    end
end
```

#### Branch Target Access
```systemverilog
// Branch target fetch
always @(posedge clk_i) begin
    if (rst_ni && branch_taken) begin
        // Fetch from branch target
        i_araddr_o <= branch_target;
        i_arvalid_o <= 1'b1;
    end
end
```

### Data Access

#### Load Operations
```systemverilog
// Load operation types
typedef enum logic [2:0] {
    LOAD_BYTE,      // LB - Load byte
    LOAD_HALF,      // LH - Load halfword
    LOAD_WORD,      // LW - Load word
    LOAD_BYTE_U,    // LBU - Load byte unsigned
    LOAD_HALF_U     // LHU - Load halfword unsigned
} load_type_e;

// Load address calculation
assign load_addr = rs1_data + immediate;
assign byte_offset = load_addr[1:0];
```

#### Store Operations
```systemverilog
// Store operation types
typedef enum logic [1:0] {
    STORE_BYTE,     // SB - Store byte
    STORE_HALF,     // SH - Store halfword
    STORE_WORD      // SW - Store word
} store_type_e;

// Store data preparation
always @(*) begin
    case (store_type)
        STORE_BYTE: begin
            case (byte_offset)
                2'b00: store_data = {24'b0, rs2_data[7:0]};
                2'b01: store_data = {16'b0, rs2_data[7:0], 8'b0};
                2'b10: store_data = {8'b0, rs2_data[7:0], 16'b0};
                2'b11: store_data = {rs2_data[7:0], 24'b0};
            endcase
            byte_enable = (4'b0001 << byte_offset);
        end
        STORE_HALF: begin
            if (byte_offset[1]) begin
                store_data = {rs2_data[15:0], 16'b0};
                byte_enable = 4'b1100;
            end else begin
                store_data = {16'b0, rs2_data[15:0]};
                byte_enable = 4'b0011;
            end
        end
        STORE_WORD: begin
            store_data = rs2_data;
            byte_enable = 4'b1111;
        end
    endcase
end
```

## Memory Alignment

### Alignment Requirements
RISC-V requires aligned memory access for optimal performance:

- **Word Access (LW/SW):** Address must be 4-byte aligned (addr[1:0] = 2'b00)
- **Halfword Access (LH/SH):** Address must be 2-byte aligned (addr[0] = 1'b0)
- **Byte Access (LB/SB):** No alignment requirement

### Alignment Handling
```systemverilog
// Alignment check
always @(*) begin
    case (mem_access_type)
        MEM_WORD:   misaligned = (mem_addr[1:0] != 2'b00);
        MEM_HALF:   misaligned = (mem_addr[0] != 1'b0);
        MEM_BYTE:   misaligned = 1'b0;
        default:    misaligned = 1'b0;
    endcase
end

// Exception generation
assign load_addr_misaligned = misaligned && mem_read_en;
assign store_addr_misaligned = misaligned && mem_write_en;
```

## Memory Performance

### Access Latency
- **Instruction Fetch:** 1-3 cycles (depending on memory wait states)
- **Data Load:** 1-3 cycles (depending on memory wait states)
- **Data Store:** 1 cycle (write-through)

### Bandwidth Analysis
- **Instruction Bandwidth:** 4 bytes per cycle (ideal)
- **Data Bandwidth:** 4 bytes per cycle (load/store)
- **Total Bandwidth:** 8 bytes per cycle (instruction + data)

### Performance Optimization

#### Pipelined Memory Access
```systemverilog
// Pipelined memory access
always @(posedge clk_i) begin
    if (rst_ni) begin
        // Stage 1: Address generation
        if (!stall_m) begin
            mem_addr_reg <= alu_result;
            mem_access_type_reg <= mem_access_type;
        end
        
        // Stage 2: Memory access
        if (mem_read_en_reg) begin
            // Initiate read transaction
            d_araddr_o <= mem_addr_reg;
            d_arvalid_o <= 1'b1;
        end
        
        // Stage 3: Data reception
        if (d_rvalid_i && d_rready_o) begin
            mem_data_reg <= d_rdata_i;
        end
    end
end
```

#### Memory Access Optimization
- **Address Prefetching:** Predict next instruction address
- **Data Prefetching:** Prefetch likely data accesses
- **Write Buffering:** Buffer writes to reduce latency
- **Access Coalescing:** Combine multiple accesses

## Memory Models

### Behavioral Memory Model
```systemverilog
module behavioral_memory #(
    parameter addr_t BASE_ADDR = 32'h0000_0000,
    parameter integer MEM_SIZE = 1024*1024  // 1MB
) (
    input  logic        clk_i,
    input  logic        rst_ni,
    
    // AXI4-Lite Read Interface
    input  logic        arvalid_i,
    output logic        arready_o,
    input  addr_t       araddr_i,
    input  logic [2:0]  arprot_i,
    
    output logic        rvalid_o,
    input  logic        rready_i,
    output word_t       rdata_o,
    output logic [1:0]  rresp_o,
    
    // AXI4-Lite Write Interface
    input  logic        awvalid_i,
    output logic        awready_o,
    input  addr_t       awaddr_i,
    input  logic [2:0]  awprot_i,
    
    input  logic        wvalid_i,
    output logic        wready_o,
    input  word_t       wdata_i,
    input  logic [3:0]  wstrb_i,
    
    output logic        bvalid_o,
    input  logic        bready_i,
    output logic [1:0]  bresp_o
);

    // Memory array
    logic [7:0] mem_array [0:MEM_SIZE-1];
    
    // Read transaction
    always @(posedge clk_i) begin
        if (arvalid_i && arready_o) begin
            // Check address range
            if (araddr_i >= BASE_ADDR && araddr_i < BASE_ADDR + MEM_SIZE) begin
                // Read data
                rdata_o <= {mem_array[araddr_i+3], mem_array[araddr_i+2], 
                           mem_array[araddr_i+1], mem_array[araddr_i]};
                rresp_o <= 2'b00;  // OKAY
            end else begin
                rresp_o <= 2'b10;  // SLVERR
            end
            rvalid_o <= 1'b1;
        end
        
        if (rvalid_o && rready_i) begin
            rvalid_o <= 1'b0;
        end
    end
    
    // Write transaction
    always @(posedge clk_i) begin
        if (wvalid_i && wready_o) begin
            // Check address range
            if (awaddr_i >= BASE_ADDR && awaddr_i < BASE_ADDR + MEM_SIZE) begin
                // Write data
                if (wstrb_i[0]) mem_array[awaddr_i] <= wdata_i[7:0];
                if (wstrb_i[1]) mem_array[awaddr_i+1] <= wdata_i[15:8];
                if (wstrb_i[2]) mem_array[awaddr_i+2] <= wdata_i[23:16];
                if (wstrb_i[3]) mem_array[awaddr_i+3] <= wdata_i[31:24];
                bresp_o <= 2'b00;  // OKAY
            end else begin
                bresp_o <= 2'b10;  // SLVERR
            end
            bvalid_o <= 1'b1;
        end
        
        if (bvalid_o && bready_i) begin
            bvalid_o <= 1'b0;
        end
    end
    
    // Handshake signals
    assign arready_o = !rvalid_o || rready_i;
    assign wready_o = !bvalid_o || bready_i;
    assign awready_o = wvalid_i && wready_o;

endmodule
```

### Cache Models
```systemverilog
// Instruction cache model (Phase 1)
module instruction_cache #(
    parameter integer CACHE_SIZE = 4096,    // 4KB
    parameter integer LINE_SIZE = 32,       // 32 bytes per line
    parameter integer WAYS = 2              // 2-way set associative
) (
    // Cache interface
    input  logic        clk_i,
    input  logic        rst_ni,
    input  addr_t       addr_i,
    input  logic        valid_i,
    output word_t       data_o,
    output logic        hit_o,
    output logic        ready_o
);

    // Cache parameters
    localparam integer NUM_SETS = CACHE_SIZE / (LINE_SIZE * WAYS);
    localparam integer SET_BITS = $clog2(NUM_SETS);
    localparam integer TAG_BITS = 32 - SET_BITS - 2;  // 2 bits for byte offset
    
    // Cache memory
    typedef struct packed {
        logic [TAG_BITS-1:0] tag;
        logic                valid;
        logic [31:0]         data [0:7];  // 8 words per line
    } cache_line_t;
    
    cache_line_t cache_mem [0:NUM_SETS-1][0:WAYS-1];
    
    // Cache access logic
    logic [SET_BITS-1:0] set_index;
    logic [TAG_BITS-1:0] tag;
    logic [WAYS-1:0]     hit_way;
    logic                cache_hit;
    
    assign set_index = addr_i[SET_BITS+1:2];
    assign tag = addr_i[31:SET_BITS+2];
    
    // Hit detection
    genvar way;
    generate
        for (way = 0; way < WAYS; way++) begin : way_gen
            assign hit_way[way] = cache_mem[set_index][way].valid && 
                                 (cache_mem[set_index][way].tag == tag);
        end
    endgenerate
    
    assign cache_hit = |hit_way;
    assign hit_o = cache_hit;
    
    // Data output
    logic [1:0] word_offset;
    assign word_offset = addr_i[3:2];
    
    always @(*) begin
        data_o = 32'h0;
        for (int way = 0; way < WAYS; way++) begin
            if (hit_way[way]) begin
                data_o = cache_mem[set_index][way].data[word_offset];
            end
        end
    end
    
    assign ready_o = 1'b1;  // Single-cycle access

endmodule
```

## Future Enhancements

### Phase 1: Instruction Cache
- **4KB 2-way Set Associative Cache**
- **32-byte Cache Lines**
- **LRU Replacement Policy**
- **Write-through Policy**

### Phase 2: Data Cache
- **8KB 4-way Set Associative Cache**
- **64-byte Cache Lines**
- **Write-back Policy**
- **Coherency Protocol**

### Phase 3: Memory Management Unit
- **TLB for Address Translation**
- **Page Table Support**
- **Memory Protection**
- **Virtual Memory Support**

---

**Memory System Version:** 1.0  
**Last Updated:** 2025-07-05  
**Core Version:** RV32IM 5-stage Pipeline 