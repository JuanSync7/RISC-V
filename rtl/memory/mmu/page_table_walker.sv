`timescale 1ns / 1ps

import mmu_pkg::*;

module page_table_walker #(
  parameter int VADDR_WIDTH = MMU_VADDR_WIDTH,
  parameter int PADDR_WIDTH = MMU_PADDR_WIDTH,
  parameter int PAGE_SIZE_BITS = MMU_PAGE_SIZE_BITS
) (
  input  logic                   clk,
  input  logic                   rst_n,

  // Request from MMU (on TLB miss)
  input  logic [VADDR_WIDTH-1:0] vaddr_i,
  input  logic                   ptw_req_valid_i,
  output logic                   ptw_req_ready_o,

  // satp register inputs
  input  logic [PADDR_WIDTH-1:0] satp_ppn_i,
  input  logic [3:0]             satp_mode_i,

  // Output to TLB (new entry)
  output tlb_entry_t             tlb_entry_o,
  output logic                   tlb_update_valid_o,
  input  logic                   tlb_update_ready_i,

  // Output to MMU (physical address, fault)
  output logic [PADDR_WIDTH-1:0] paddr_o,
  output logic                   ptw_done_o,
  output logic                   fault_o,
  output logic [3:0]             fault_type_o,

  // Memory interface (AXI4-Lite for now)
  output logic                   mem_arvalid_o,
  input  logic                   mem_arready_i,
  output logic [PADDR_WIDTH-1:0] mem_araddr_o,
  input  logic [31:0]            mem_rdata_i,
  input  logic                   mem_rvalid_i,
  output logic                   mem_rready_o,
  input  logic [1:0]             mem_rresp_i
);

  // Derived parameters
  localparam int VPN_WIDTH = VADDR_WIDTH - PAGE_SIZE_BITS;
  localparam int PPN_WIDTH = PADDR_WIDTH - PAGE_SIZE_BITS;

  // Page Table Entry (PTE) format (simplified for now, assuming 32-bit PTEs)
  typedef struct packed {
    logic [PPN_WIDTH-1:0] ppn; // Physical Page Number
    logic                 rsw; // Reserved for software
    logic                 d;   // Dirty
    logic                 a;   // Accessed
    logic                 g;   // Global
    logic                 u;   // User
    logic                 x;   // Executable
    logic                 w;   // Writable
    logic                 r;   // Readable
    logic                 v;   // Valid
  } pte_t;

  // State machine for page table walk
  mmu_state_e current_state, next_state;

  // Internal registers
  logic [VADDR_WIDTH-1:0] ptw_vaddr_reg;
  logic [PADDR_WIDTH-1:0] pte_addr_reg; // Address of the PTE in memory
  pte_t                   fetched_pte_reg;

  // State transitions
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= MMU_IDLE;
    end else begin
      current_state <= next_state;
    end
  end

  // Next state logic and output assignments
  always_comb begin
    next_state = current_state;
    ptw_req_ready_o = 1'b0;
    tlb_update_valid_o = 1'b0;
    tlb_entry_o = '0;
    paddr_o = '0;
    ptw_done_o = 1'b0;
    fault_o = 1'b0;
    fault_type_o = '0;
    mem_arvalid_o = 1'b0;
    mem_araddr_o = '0;
    mem_rready_o = 1'b0;

    case (current_state)
      MMU_IDLE:
        if (ptw_req_valid_i) begin
          ptw_vaddr_reg = vaddr_i;
          // TODO: Get satp base address from CSRs
          // For now, assume a fixed base address for page table level 0
          pte_addr_reg = satp_ppn_i;
          next_state = MMU_PTW_FETCH_PTE;
          ptw_req_ready_o = 1'b1;
        end

      MMU_PTW_FETCH_PTE:
        begin
          mem_arvalid_o = 1'b1;
          mem_araddr_o = pte_addr_reg;
          mem_rready_o = 1'b1;

          if (mem_arvalid_o && mem_arready_i && mem_rvalid_i && mem_rready_o) begin
            fetched_pte_reg.v = mem_rdata_i[0];
            fetched_pte_reg.r = mem_rdata_i[1];
            fetched_pte_reg.w = mem_rdata_i[2];
            fetched_pte_reg.x = mem_rdata_i[3];
            fetched_pte_reg.u = mem_rdata_i[4];
            fetched_pte_reg.g = mem_rdata_i[5];
            fetched_pte_reg.a = mem_rdata_i[6];
            fetched_pte_reg.d = mem_rdata_i[7];
            fetched_pte_reg.rsw = mem_rdata_i[9:8];
            fetched_pte_reg.ppn = mem_rdata_i[MMU_PADDR_WIDTH-1 : MMU_PAGE_SIZE_BITS];

            next_state = MMU_PTW_TRANSLATE;
          end
        end

      MMU_PTW_TRANSLATE:
        begin
          if (fetched_pte_reg.v == 1'b0) begin
            // Invalid PTE, generate page fault
            fault_o = 1'b1;
            fault_type_o = 4'hC; // Page fault (instruction/load/store)
            ptw_done_o = 1'b1;
            next_state = MMU_IDLE;
          end else begin
            // Valid PTE, construct physical address and update TLB
            paddr_o = {fetched_pte_reg.ppn, ptw_vaddr_reg[PAGE_SIZE_BITS-1:0]};
            ptw_done_o = 1'b1;

            tlb_entry_o.vpn = ptw_vaddr_reg[VADDR_WIDTH-1:PAGE_SIZE_BITS];
            tlb_entry_o.ppn = fetched_pte_reg.ppn;
            tlb_entry_o.valid = 1'b1;
            tlb_entry_o.dirty = fetched_pte_reg.d;
            tlb_entry_o.accessed = fetched_pte_reg.a;
            tlb_entry_o.global = fetched_pte_reg.g;
            tlb_entry_o.user = fetched_pte_reg.u;
            tlb_entry_o.read = fetched_pte_reg.r;
            tlb_entry_o.write = fetched_pte_reg.w;
            tlb_entry_o.execute = fetched_pte_reg.x;
            tlb_entry_o.rsvd = '0;

            tlb_update_valid_o = 1'b1;
            if (tlb_update_valid_o && tlb_update_ready_i) begin
              next_state = MMU_IDLE;
            end
          end
        end

      default:
        next_state = MMU_IDLE;
    endcase
  end

endmodule
