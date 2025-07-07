# Memory Management Unit (MMU) Module Structure

This directory contains the SystemVerilog modules for the RISC-V Memory Management Unit (MMU).

## Overview

The MMU is responsible for translating virtual addresses to physical addresses, enforcing memory protection, and managing virtual memory. It consists of the following sub-modules:

- **`mmu.sv`**: The top-level MMU module that integrates the TLB, Page Table Walker, and MMU CSRs.
- **`tlb.sv`**: Implements the Translation Lookaside Buffer, a cache for recent virtual-to-physical address translations.
- **`page_table_walker.sv`**: Handles page table lookups in main memory when a TLB miss occurs.
- **`mmu_csr.sv`**: Manages MMU-specific Control and Status Registers (CSRs), such as `satp`.
- **`mmu_pkg.sv`**: A package defining common data types and parameters used across the MMU modules.

## Integration

The MMU is instantiated within the `core_subsystem.sv` module. Instruction fetch requests from `fetch_stage.sv` and data access requests from `execute_stage.sv` are routed through the MMU for address translation before being sent to the L1 caches (`icache.sv` and `dcache.sv`).

## Configuration

The MMU's behavior is configurable through parameters defined in `mmu_pkg.sv`, including:

- `MMU_TLB_SIZE`: Number of entries in the TLB.
- `MMU_TLB_ASSOC`: TLB associativity.
- `MMU_PAGE_SIZE_BITS`: Log2 of the page size (e.g., 12 for 4KB pages).
- `MMU_VADDR_WIDTH`: Virtual address width.
- `MMU_PADDR_WIDTH`: Physical address width.

## Future Enhancements

- Support for different page table levels (e.g., Sv39, Sv48).
- More sophisticated TLB replacement policies (e.g., true LRU, pseudo-LRU).
- Hardware performance counters for MMU activity (TLB hits/misses, PTW cycles).
- Integration with a more comprehensive CSR management unit.
