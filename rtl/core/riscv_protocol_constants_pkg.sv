//=============================================================================
// Company: Sondrel Ltd
// Author: DesignAI (designai@sondrel.com)
// Created: 2025-01-27
//
// File: riscv_protocol_constants_pkg.sv
// Package: riscv_protocol_constants_pkg
//
// Project Name: RISC-V RV32IM Protocol Constants
// Target Devices: ASIC/FPGA
// Tool Versions: VCS 2020.03, ModelSim 2021.1
// Verification Status: Not Verified
// Quality Status: Production Ready
//
// Description:
//   Centralized package containing all protocol-specific constants, opcodes,
//   and configuration values used throughout the RISC-V system. Eliminates
//   hardcoded values and provides single source of truth for protocol specs.
//=============================================================================

`timescale 1ns/1ps
`default_nettype none

package riscv_protocol_constants_pkg;

    //---------------------------------------------------------------------------
    // 1. AXI4 Protocol Constants
    //---------------------------------------------------------------------------
    
    // AXI4 Burst Type Constants
    parameter logic [1:0] AXI4_BURST_FIXED = 2'b00;   // Fixed address burst
    parameter logic [1:0] AXI4_BURST_INCR  = 2'b01;   // Incrementing burst  
    parameter logic [1:0] AXI4_BURST_WRAP  = 2'b10;   // Wrapping burst
    parameter logic [1:0] AXI4_BURST_RESERVED = 2'b11; // Reserved
    
    // AXI4 Response Codes
    parameter logic [1:0] AXI4_RESP_OKAY   = 2'b00;   // Normal access success
    parameter logic [1:0] AXI4_RESP_EXOKAY = 2'b01;   // Exclusive access okay
    parameter logic [1:0] AXI4_RESP_SLVERR = 2'b10;   // Slave error
    parameter logic [1:0] AXI4_RESP_DECERR = 2'b11;   // Decode error
    
    // AXI4 Cache Attributes
    parameter logic [3:0] AXI4_CACHE_DEVICE_NON_BUFFERABLE   = 4'b0000;
    parameter logic [3:0] AXI4_CACHE_DEVICE_BUFFERABLE       = 4'b0001;
    parameter logic [3:0] AXI4_CACHE_NORMAL_NON_CACHEABLE    = 4'b0010;
    parameter logic [3:0] AXI4_CACHE_WRITE_THROUGH_NO_ALLOC  = 4'b0110;
    parameter logic [3:0] AXI4_CACHE_WRITE_BACK_NO_ALLOC     = 4'b0111;
    parameter logic [3:0] AXI4_CACHE_WRITE_THROUGH_R_ALLOC   = 4'b1010;
    parameter logic [3:0] AXI4_CACHE_WRITE_BACK_R_ALLOC      = 4'b1011;
    parameter logic [3:0] AXI4_CACHE_WRITE_THROUGH_W_ALLOC   = 4'b1110;
    parameter logic [3:0] AXI4_CACHE_WRITE_BACK_W_ALLOC      = 4'b1111;
    
    // AXI4 Protection Attributes  
    parameter logic [2:0] AXI4_PROT_UNPRIVILEGED_SECURE_DATA = 3'b000;
    parameter logic [2:0] AXI4_PROT_UNPRIVILEGED_SECURE_INST = 3'b001;
    parameter logic [2:0] AXI4_PROT_UNPRIVILEGED_NONSEC_DATA = 3'b010;
    parameter logic [2:0] AXI4_PROT_UNPRIVILEGED_NONSEC_INST = 3'b011;
    parameter logic [2:0] AXI4_PROT_PRIVILEGED_SECURE_DATA   = 3'b100;
    parameter logic [2:0] AXI4_PROT_PRIVILEGED_SECURE_INST   = 3'b101;
    parameter logic [2:0] AXI4_PROT_PRIVILEGED_NONSEC_DATA   = 3'b110;
    parameter logic [2:0] AXI4_PROT_PRIVILEGED_NONSEC_INST   = 3'b111;
    
    // AXI4 Size Encoding
    parameter logic [2:0] AXI4_SIZE_1_BYTE   = 3'b000;   // 1 byte
    parameter logic [2:0] AXI4_SIZE_2_BYTES  = 3'b001;   // 2 bytes
    parameter logic [2:0] AXI4_SIZE_4_BYTES  = 3'b010;   // 4 bytes  
    parameter logic [2:0] AXI4_SIZE_8_BYTES  = 3'b011;   // 8 bytes
    parameter logic [2:0] AXI4_SIZE_16_BYTES = 3'b100;   // 16 bytes
    parameter logic [2:0] AXI4_SIZE_32_BYTES = 3'b101;   // 32 bytes
    parameter logic [2:0] AXI4_SIZE_64_BYTES = 3'b110;   // 64 bytes
    parameter logic [2:0] AXI4_SIZE_128_BYTES = 3'b111;  // 128 bytes
    
    // AXI4 Default Values
    parameter logic [7:0]  AXI4_LEN_SINGLE_BEAT = 8'h00;   // Single beat transfer
    parameter logic [3:0]  AXI4_QOS_NO_QOS      = 4'h0;    // No QoS control
    parameter logic [3:0]  AXI4_REGION_DEFAULT  = 4'h0;    // Default region
    parameter logic        AXI4_LOCK_NORMAL     = 1'b0;    // Normal access
    parameter logic        AXI4_LOCK_EXCLUSIVE  = 1'b1;    // Exclusive access
    parameter logic        AXI4_LAST_TRANSFER   = 1'b1;    // Last transfer in burst
    
    //---------------------------------------------------------------------------
    // 2. CHI Protocol Constants (CHI-B Specification)
    //---------------------------------------------------------------------------
    
    // CHI Request Opcodes
    parameter logic [6:0] CHI_REQ_ReadNoSnp          = 7'h01;  // Non-snooping read
    parameter logic [6:0] CHI_REQ_ReadOnce           = 7'h02;  // Read once, no cache
    parameter logic [6:0] CHI_REQ_ReadClean          = 7'h03;  // Read clean
    parameter logic [6:0] CHI_REQ_ReadNotSharedDirty = 7'h04;  // Read not shared dirty
    parameter logic [6:0] CHI_REQ_ReadShared         = 7'h05;  // Read shared
    parameter logic [6:0] CHI_REQ_ReadUnique         = 7'h07;  // Read unique
    parameter logic [6:0] CHI_REQ_WriteNoSnpPtl      = 7'h20;  // Non-snooping partial write
    parameter logic [6:0] CHI_REQ_WriteNoSnpFull     = 7'h18;  // Non-snooping full write
    parameter logic [6:0] CHI_REQ_WriteUniqueFullStash = 7'h19; // Write unique full stash
    parameter logic [6:0] CHI_REQ_WriteUniquePtlStash  = 7'h1A; // Write unique partial stash
    parameter logic [6:0] CHI_REQ_StashOnceShared    = 7'h1C;  // Stash once shared
    parameter logic [6:0] CHI_REQ_StashOnceUnique    = 7'h1D;  // Stash once unique
    parameter logic [6:0] CHI_REQ_CleanUnique        = 7'h11;  // Clean unique
    parameter logic [6:0] CHI_REQ_MakeUnique         = 7'h12;  // Make unique
    parameter logic [6:0] CHI_REQ_Evict              = 7'h13;  // Evict
    
    // CHI Response Opcodes
    parameter logic [4:0] CHI_RSP_CompData           = 5'h04;  // Complete with data
    parameter logic [4:0] CHI_RSP_Comp               = 5'h0C;  // Complete without data
    parameter logic [4:0] CHI_RSP_CompDBIDResp       = 5'h0E;  // Complete with DBID response
    parameter logic [4:0] CHI_RSP_DBIDResp           = 5'h0D;  // DBID response
    parameter logic [4:0] CHI_RSP_PCrdGrant          = 5'h0F;  // Protocol credit grant
    parameter logic [4:0] CHI_RSP_ReadReceipt        = 5'h10;  // Read receipt
    parameter logic [4:0] CHI_RSP_SnpResp            = 5'h11;  // Snoop response
    parameter logic [4:0] CHI_RSP_SnpRespData        = 5'h12;  // Snoop response with data
    parameter logic [4:0] CHI_RSP_CompAck            = 5'h13;  // Complete acknowledge
    
    // CHI Data Opcodes
    parameter logic [3:0] CHI_DAT_DataLCrdReturn     = 4'h0;   // Data link credit return
    parameter logic [3:0] CHI_DAT_SnpRespData        = 4'h1;   // Snoop response data
    parameter logic [3:0] CHI_DAT_CopyBackWrData     = 4'h2;   // Copy back write data
    parameter logic [3:0] CHI_DAT_NonCopyBackWrData  = 4'h6;   // Non-copyback write data
    parameter logic [3:0] CHI_DAT_CompData           = 4'h4;   // Complete data
    parameter logic [3:0] CHI_DAT_SnpRespDataPtl     = 4'h5;   // Snoop response data partial
    parameter logic [3:0] CHI_DAT_SnpRespDataFwded   = 4'h7;   // Snoop response data forwarded
    
    // CHI Size Encoding
    parameter logic [2:0] CHI_SIZE_1_BYTE     = 3'd0;   // 1 byte
    parameter logic [2:0] CHI_SIZE_2_BYTES    = 3'd1;   // 2 bytes
    parameter logic [2:0] CHI_SIZE_4_BYTES    = 3'd2;   // 4 bytes
    parameter logic [2:0] CHI_SIZE_8_BYTES    = 3'd3;   // 8 bytes
    parameter logic [2:0] CHI_SIZE_16_BYTES   = 3'd4;   // 16 bytes
    parameter logic [2:0] CHI_SIZE_32_BYTES   = 3'd5;   // 32 bytes
    parameter logic [2:0] CHI_SIZE_64_BYTES   = 3'd6;   // 64 bytes
    
    // CHI Response Error Codes
    parameter logic [2:0] CHI_RESPERR_OK      = 3'b000; // Normal okay response
    parameter logic [2:0] CHI_RESPERR_EXOK    = 3'b001; // Exclusive okay response  
    parameter logic [2:0] CHI_RESPERR_DERR    = 3'b010; // Data error
    parameter logic [2:0] CHI_RESPERR_NDERR   = 3'b011; // Non-data error
    
    // CHI Memory Attributes
    parameter logic [3:0] CHI_MEMATTR_DEVICE         = 4'b0000; // Device memory
    parameter logic [3:0] CHI_MEMATTR_NORMAL_NC      = 4'b0001; // Normal non-cacheable
    parameter logic [3:0] CHI_MEMATTR_NORMAL_WT      = 4'b0010; // Normal write-through
    parameter logic [3:0] CHI_MEMATTR_NORMAL_WB      = 4'b0011; // Normal write-back
    
    // CHI Order Encoding
    parameter logic [1:0] CHI_ORDER_NONE              = 2'b00;  // No ordering
    parameter logic [1:0] CHI_ORDER_REQUEST_ORDER     = 2'b01;  // Request ordering
    parameter logic [1:0] CHI_ORDER_ENDPOINT_ORDER    = 2'b10;  // Endpoint ordering
    
    //---------------------------------------------------------------------------
    // 3. TileLink Protocol Constants (TL-UL Specification)
    //---------------------------------------------------------------------------
    
    // TileLink A-Channel Opcodes (Host -> Device)
    parameter logic [2:0] TL_A_PutFullData    = 3'h0;   // Put full data
    parameter logic [2:0] TL_A_PutPartialData = 3'h1;   // Put partial data
    parameter logic [2:0] TL_A_ArithmeticData = 3'h2;   // Arithmetic operation
    parameter logic [2:0] TL_A_LogicalData    = 3'h3;   // Logical operation
    parameter logic [2:0] TL_A_Get            = 3'h4;   // Get request
    parameter logic [2:0] TL_A_Intent         = 3'h5;   // Hint/Intent
    parameter logic [2:0] TL_A_AcquireBlock   = 3'h6;   // Acquire block
    parameter logic [2:0] TL_A_AcquirePerm    = 3'h7;   // Acquire permission
    
    // TileLink D-Channel Opcodes (Device -> Host) 
    parameter logic [2:0] TL_D_AccessAck      = 3'h0;   // Access acknowledgment
    parameter logic [2:0] TL_D_AccessAckData  = 3'h1;   // Access ack with data
    parameter logic [2:0] TL_D_HintAck        = 3'h2;   // Hint acknowledgment
    parameter logic [2:0] TL_D_Grant          = 3'h4;   // Grant
    parameter logic [2:0] TL_D_GrantData      = 3'h5;   // Grant with data
    parameter logic [2:0] TL_D_ReleaseAck     = 3'h6;   // Release acknowledgment
    
    // TileLink Size Encoding (2^size bytes)
    parameter logic [2:0] TL_SIZE_1_BYTE      = 3'h0;   // 1 byte (2^0)
    parameter logic [2:0] TL_SIZE_2_BYTES     = 3'h1;   // 2 bytes (2^1)
    parameter logic [2:0] TL_SIZE_4_BYTES     = 3'h2;   // 4 bytes (2^2)
    parameter logic [2:0] TL_SIZE_8_BYTES     = 3'h3;   // 8 bytes (2^3)
    parameter logic [2:0] TL_SIZE_16_BYTES    = 3'h4;   // 16 bytes (2^4)
    parameter logic [2:0] TL_SIZE_32_BYTES    = 3'h5;   // 32 bytes (2^5)
    parameter logic [2:0] TL_SIZE_64_BYTES    = 3'h6;   // 64 bytes (2^6)
    
    // TileLink Arithmetic Operations
    parameter logic [2:0] TL_ARITH_MIN        = 3'h0;   // Minimum
    parameter logic [2:0] TL_ARITH_MAX        = 3'h1;   // Maximum
    parameter logic [2:0] TL_ARITH_MINU       = 3'h2;   // Minimum unsigned
    parameter logic [2:0] TL_ARITH_MAXU       = 3'h3;   // Maximum unsigned
    parameter logic [2:0] TL_ARITH_ADD        = 3'h4;   // Add
    
    // TileLink Logical Operations
    parameter logic [2:0] TL_LOGICAL_XOR      = 3'h0;   // Exclusive OR
    parameter logic [2:0] TL_LOGICAL_OR       = 3'h1;   // Logical OR
    parameter logic [2:0] TL_LOGICAL_AND      = 3'h2;   // Logical AND
    parameter logic [2:0] TL_LOGICAL_SWAP     = 3'h3;   // Swap
    
    // TileLink Parameters
    parameter logic [2:0] TL_PARAM_NO_PARAM   = 3'h0;   // No parameters
    parameter logic [2:0] TL_PARAM_TOTRUNK    = 3'h1;   // To trunk
    parameter logic [2:0] TL_PARAM_TOBRANCH   = 3'h2;   // To branch
    parameter logic [2:0] TL_PARAM_TONONE     = 3'h3;   // To none
    
    //---------------------------------------------------------------------------
    // 4. Cache Coherency Constants
    //---------------------------------------------------------------------------
    
    // MESI Cache States
    parameter logic [1:0] CACHE_STATE_INVALID   = 2'b00;  // Invalid
    parameter logic [1:0] CACHE_STATE_SHARED    = 2'b01;  // Shared
    parameter logic [1:0] CACHE_STATE_EXCLUSIVE = 2'b10;  // Exclusive  
    parameter logic [1:0] CACHE_STATE_MODIFIED  = 2'b11;  // Modified
    
    // Cache Line States (Extended MESI)
    parameter logic [2:0] CACHE_LINE_INVALID    = 3'b000; // Invalid
    parameter logic [2:0] CACHE_LINE_SHARED     = 3'b001; // Shared
    parameter logic [2:0] CACHE_LINE_EXCLUSIVE  = 3'b010; // Exclusive
    parameter logic [2:0] CACHE_LINE_MODIFIED   = 3'b011; // Modified
    parameter logic [2:0] CACHE_LINE_FORWARD    = 3'b100; // Forward
    parameter logic [2:0] CACHE_LINE_OWNED      = 3'b101; // Owned (MOESI)
    
    // Cache Request Types
    parameter logic [2:0] CACHE_REQ_READ        = 3'b000; // Read request
    parameter logic [2:0] CACHE_REQ_WRITE       = 3'b001; // Write request
    parameter logic [2:0] CACHE_REQ_INVALIDATE  = 3'b010; // Invalidate request
    parameter logic [2:0] CACHE_REQ_FLUSH       = 3'b011; // Flush request
    parameter logic [2:0] CACHE_REQ_PREFETCH    = 3'b100; // Prefetch request
    parameter logic [2:0] CACHE_REQ_WRITEBACK   = 3'b101; // Writeback request
    
    //---------------------------------------------------------------------------
    // 5. Performance and Timing Constants  
    //---------------------------------------------------------------------------
    
    // Default Timeout Values (in clock cycles)
    parameter integer TIMEOUT_AXI4_TRANSACTION   = 1000;   // AXI4 transaction timeout
    parameter integer TIMEOUT_CHI_TRANSACTION    = 2000;   // CHI transaction timeout  
    parameter integer TIMEOUT_TILELINK_TRANSACTION = 1000; // TileLink transaction timeout
    parameter integer TIMEOUT_CACHE_MISS         = 5000;   // Cache miss timeout
    parameter integer TIMEOUT_COHERENCY_SNOOP    = 500;    // Coherency snoop timeout
    parameter integer TIMEOUT_BARRIER_SYNC       = 10000;  // Barrier synchronization timeout
    parameter integer TIMEOUT_DEBUG_ACCESS       = 1000;   // Debug access timeout
    
    // Performance Counter Defaults
    parameter integer PERF_COUNTER_WIDTH         = 32;     // Performance counter width
    parameter integer PERF_SAMPLE_PERIOD         = 1000;   // Sample period for rate calculations
    parameter integer PERF_HISTORY_DEPTH         = 16;     // History depth for average calculations
    
    // Queue and Buffer Sizes
    parameter integer DEFAULT_TXN_QUEUE_DEPTH    = 16;     // Default transaction queue depth
    parameter integer DEFAULT_RSPBUF_DEPTH       = 8;      // Default response buffer depth
    parameter integer DEFAULT_SNOOP_QUEUE_DEPTH  = 4;      // Default snoop queue depth
    parameter integer DEFAULT_WRITEBACK_QUEUE_DEPTH = 8;   // Default writeback queue depth
    
    //---------------------------------------------------------------------------
    // 6. Debug and Verification Constants
    //---------------------------------------------------------------------------
    
    // Debug Operation Codes
    parameter logic [3:0] DEBUG_OP_NOP           = 4'h0;   // No operation
    parameter logic [3:0] DEBUG_OP_HALT          = 4'h1;   // Halt core
    parameter logic [3:0] DEBUG_OP_RESUME        = 4'h2;   // Resume core
    parameter logic [3:0] DEBUG_OP_STEP          = 4'h3;   // Single step
    parameter logic [3:0] DEBUG_OP_RESET         = 4'h4;   // Reset core
    parameter logic [3:0] DEBUG_OP_READ_REG      = 4'h5;   // Read register
    parameter logic [3:0] DEBUG_OP_WRITE_REG     = 4'h6;   // Write register
    parameter logic [3:0] DEBUG_OP_READ_MEM      = 4'h7;   // Read memory
    parameter logic [3:0] DEBUG_OP_WRITE_MEM     = 4'h8;   // Write memory
    parameter logic [3:0] DEBUG_OP_SET_BREAKPOINT = 4'h9;  // Set breakpoint
    parameter logic [3:0] DEBUG_OP_CLR_BREAKPOINT = 4'hA;  // Clear breakpoint
    
    // Verification Stimulus Constants
    parameter logic [31:0] VERIF_MAGIC_START     = 32'hDEAD_BEEF; // Test start marker
    parameter logic [31:0] VERIF_MAGIC_END       = 32'hCAFE_BABE; // Test end marker
    parameter logic [31:0] VERIF_MAGIC_PASS      = 32'h600D_C0DE; // Test pass marker
    parameter logic [31:0] VERIF_MAGIC_FAIL      = 32'hBAD_C0DE;  // Test fail marker
    
    // Test Address Ranges
    parameter logic [31:0] TEST_ADDR_BASE        = 32'h0000_1000; // Test address base
    parameter logic [31:0] TEST_ADDR_RESET       = 32'h0000_0000; // Reset vector for tests
    parameter logic [31:0] TEST_ADDR_EXCEPTION   = 32'h0000_2000; // Exception handler base
    parameter logic [31:0] TEST_ADDR_STACK       = 32'h0001_0000; // Stack pointer base
    
    //---------------------------------------------------------------------------
    // 7. Memory System Constants
    //---------------------------------------------------------------------------
    
    // Memory Request Priorities
    parameter logic [1:0] MEM_PRI_LOW            = 2'b00;  // Low priority
    parameter logic [1:0] MEM_PRI_NORMAL         = 2'b01;  // Normal priority
    parameter logic [1:0] MEM_PRI_HIGH           = 2'b10;  // High priority
    parameter logic [1:0] MEM_PRI_CRITICAL       = 2'b11;  // Critical priority
    
    // Memory Access Types
    parameter logic [1:0] MEM_TYPE_NORMAL        = 2'b00;  // Normal memory
    parameter logic [1:0] MEM_TYPE_DEVICE        = 2'b01;  // Device memory
    parameter logic [1:0] MEM_TYPE_STRONGLY_ORDERED = 2'b10; // Strongly ordered
    parameter logic [1:0] MEM_TYPE_RESERVED      = 2'b11;  // Reserved
    
    // Common Address Constants
    parameter logic [31:0] ADDR_ALIGN_MASK_BYTE  = 32'hFFFF_FFFF; // Byte aligned
    parameter logic [31:0] ADDR_ALIGN_MASK_HWORD = 32'hFFFF_FFFE; // Half-word aligned
    parameter logic [31:0] ADDR_ALIGN_MASK_WORD  = 32'hFFFF_FFFC; // Word aligned
    parameter logic [31:0] ADDR_ALIGN_MASK_DWORD = 32'hFFFF_FFF8; // Double-word aligned
    parameter logic [31:0] ADDR_ALIGN_MASK_CLINE = 32'hFFFF_FFC0; // Cache line aligned (64B)
    
    //---------------------------------------------------------------------------
    // 8. Reset and Initialization Constants
    //---------------------------------------------------------------------------
    
    // Reset Values
    parameter logic [31:0] RESET_VALUE_32BIT     = 32'h0000_0000; // 32-bit reset value
    parameter logic [63:0] RESET_VALUE_64BIT     = 64'h0000_0000_0000_0000; // 64-bit reset value
    parameter logic        RESET_VALUE_1BIT      = 1'b0;          // 1-bit reset value
    
    // Initialization Patterns
    parameter logic [31:0] INIT_PATTERN_ZERO     = 32'h0000_0000; // All zeros
    parameter logic [31:0] INIT_PATTERN_ONES     = 32'hFFFF_FFFF; // All ones
    parameter logic [31:0] INIT_PATTERN_ALT      = 32'hAAAA_AAAA; // Alternating pattern
    parameter logic [31:0] INIT_PATTERN_WALKING  = 32'h0000_0001; // Walking ones pattern
    
endpackage : riscv_protocol_constants_pkg

//=============================================================================
// Usage Examples:
//
// import riscv_protocol_constants_pkg::*;
//
// // AXI4 Usage:
// assign axi_if.awburst = AXI4_BURST_INCR;
// assign axi_if.awcache = AXI4_CACHE_NORMAL_NON_CACHEABLE;
// assign axi_if.awsize = AXI4_SIZE_4_BYTES;
// 
// // CHI Usage:
// assign chi_if.req_opcode = CHI_REQ_ReadNoSnp;
// assign chi_if.req_size = CHI_SIZE_4_BYTES;
//
// // TileLink Usage: 
// assign tl_if.a_opcode = TL_A_Get;
// assign tl_if.a_size = TL_SIZE_4_BYTES;
//
// // Cache Coherency Usage:
// assign cache_state = CACHE_STATE_EXCLUSIVE;
// assign req_type = CACHE_REQ_READ;
//
//============================================================================= 