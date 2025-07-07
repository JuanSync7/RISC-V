package mmu_pkg;

  import riscv_config_pkg::*;

  // MMU configuration parameters
  parameter int MMU_TLB_SIZE = DEFAULT_MMU_TLB_SIZE; // Number of entries in TLB
  parameter int MMU_TLB_ASSOC = DEFAULT_MMU_TLB_ASSOC; // TLB associativity (e.g., 2-way set associative)
  parameter int MMU_PAGE_SIZE_BITS = CONFIG_MMU_PAGE_SIZE_BITS; // Log2 of page size (e.g., 12 for 4KB pages)
  parameter int MMU_VADDR_WIDTH = ADDR_WIDTH; // Virtual address width
  parameter int MMU_PADDR_WIDTH = ADDR_WIDTH; // Physical address width

  // Derived parameters
  localparam int MMU_VPN_WIDTH = MMU_VADDR_WIDTH - MMU_PAGE_SIZE_BITS; // Virtual Page Number width
  localparam int MMU_PPN_WIDTH = MMU_PADDR_WIDTH - MMU_PAGE_SIZE_BITS; // Physical Page Number width
  localparam int MMU_TLB_INDEX_WIDTH = $clog2(MMU_TLB_SIZE / MMU_TLB_ASSOC); // TLB index width
  localparam int MMU_TLB_TAG_WIDTH = MMU_VPN_WIDTH - MMU_TLB_INDEX_WIDTH; // TLB tag width

  // MMU states for page table walk (simplified for now)
  typedef enum logic [2:0] {
    MMU_IDLE,
    MMU_PTW_FETCH_PTE,
    MMU_PTW_TRANSLATE,
    MMU_TRANSLATE_DONE
  } mmu_state_e;

  // TLB entry structure
  typedef struct packed {
    logic [MMU_VPN_WIDTH-1:0] vpn; // Virtual Page Number
    logic [MMU_PPN_WIDTH-1:0] ppn; // Physical Page Number
    logic                     valid; // Entry is valid
    logic                     dirty; // Page has been written to
    logic                     accessed; // Page has been accessed
    logic                     global; // Global mapping
    logic                     user; // User-mode access
    logic                     read; // Read permission
    logic                     write; // Write permission
    logic                     execute; // Execute permission
    logic [1:0]               rsvd; // Reserved bits
  } tlb_entry_t;

  // MMU request/response types
  typedef struct packed {
    logic [MMU_VADDR_WIDTH-1:0] vaddr; // Virtual address
    logic                       is_write; // Is a write access
    logic                       is_fetch; // Is an instruction fetch
  } mmu_request_t;

  typedef struct packed {
    logic [MMU_PADDR_WIDTH-1:0] paddr; // Physical address
    logic                       hit; // TLB hit
    logic                       fault; // Page fault occurred
    logic [3:0]                 fault_type; // Type of fault
  } mmu_response_t;

endpackage
