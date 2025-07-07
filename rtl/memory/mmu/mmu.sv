`timescale 1ns / 1ps

import mmu_pkg::*;

module mmu #(
  parameter int VADDR_WIDTH = MMU_VADDR_WIDTH,
  parameter int PADDR_WIDTH = MMU_PADDR_WIDTH,
  parameter int TLB_SIZE = MMU_TLB_SIZE,
  parameter int TLB_ASSOC = MMU_TLB_ASSOC,
  parameter int PAGE_SIZE_BITS = MMU_PAGE_SIZE_BITS
) (
  input  logic                   clk,
  input  logic                   rst_n,

  // MMU request from CPU
  input  mmu_request_t           mmu_req_i,
  input  logic                   mmu_req_valid_i,
  output logic                   mmu_req_ready_o,

  // MMU response to CPU
  output mmu_response_t          mmu_resp_o,
  output logic                   mmu_resp_valid_o,
  input  logic                   mmu_resp_ready_i,

  // Memory interface for Page Table Walker (AXI4-Lite)
  output logic                   mem_arvalid_o,
  input  logic                   mem_arready_i,
  output logic [PADDR_WIDTH-1:0] mem_araddr_o,
  input  logic [31:0]            mem_rdata_i,
  input  logic                   mem_rvalid_i,
  output logic                   mem_rready_o,
  input  logic [1:0]             mem_rresp_i,

  // CSR interface (for satp register access)
  input  logic                   csr_read_en_i,
  input  logic [11:0]            csr_addr_i,
  output logic [31:0]            csr_rdata_o,
  input  logic                   csr_write_en_i,
  input  logic [11:0]            csr_addr_w_i,
  input  logic [31:0]            csr_wdata_i
);

  // Internal signals for TLB and PTW communication
  logic [PADDR_WIDTH-1:0] tlb_paddr;
  logic                   tlb_hit;
  logic                   tlb_fault;
  logic [3:0]             tlb_fault_type;
  logic                   tlb_req_ready;

  logic                   ptw_req_valid;
  logic                   ptw_req_ready;
  logic [VADDR_WIDTH-1:0] ptw_vaddr;
  logic [PADDR_WIDTH-1:0] ptw_paddr;
  logic                   ptw_done;
  logic                   ptw_fault;
  logic [3:0]             ptw_fault_type;

  tlb_entry_t             tlb_update_entry;
  logic                   tlb_update_valid;
  logic                   tlb_update_ready;

  logic [PADDR_WIDTH-1:0] satp_ppn;
  logic [3:0]             satp_mode;

  // Instantiate TLB
  tlb #(
    .TLB_SIZE(TLB_SIZE),
    .TLB_ASSOC(TLB_ASSOC),
    .VADDR_WIDTH(VADDR_WIDTH),
    .PADDR_WIDTH(PADDR_WIDTH),
    .PAGE_SIZE_BITS(PAGE_SIZE_BITS)
  ) i_tlb (
    .clk(clk),
    .rst_n(rst_n),
    .mmu_req_i(mmu_req_i),
    .req_valid_i(mmu_req_valid_i),
    .req_ready_o(tlb_req_ready),
    .paddr_o(tlb_paddr),
    .hit_o(tlb_hit),
    .fault_o(tlb_fault),
    .fault_type_o(tlb_fault_type),
    .tlb_entry_i(tlb_update_entry),
    .tlb_update_valid_i(tlb_update_valid),
    .tlb_update_ready_o(tlb_update_ready),
    .tlb_invalidate_valid_i(1'b0), // TODO: Connect to invalidate signals
    .tlb_invalidate_vaddr_i('0),
    .tlb_invalidate_ready_o()
  );

  // Instantiate Page Table Walker
  page_table_walker #(
    .VADDR_WIDTH(VADDR_WIDTH),
    .PADDR_WIDTH(PADDR_WIDTH),
    .PAGE_SIZE_BITS(PAGE_SIZE_BITS)
  ) i_ptw (
    .clk(clk),
    .rst_n(rst_n),
    .vaddr_i(ptw_vaddr),
    .ptw_req_valid_i(ptw_req_valid),
    .ptw_req_ready_o(ptw_req_ready),
    .tlb_entry_o(tlb_update_entry),
    .tlb_update_valid_o(tlb_update_valid),
    .tlb_update_ready_i(tlb_update_ready),
    .paddr_o(ptw_paddr),
    .ptw_done_o(ptw_done),
    .fault_o(ptw_fault),
    .fault_type_o(ptw_fault_type),
    .mem_arvalid_o(mem_arvalid_o),
    .mem_arready_i(mem_arready_i),
    .mem_araddr_o(mem_araddr_o),
    .mem_rdata_i(mem_rdata_i),
    .mem_rvalid_i(mem_rvalid_i),
    .mem_rready_o(mem_rready_o),
    .mem_rresp_i(mem_rresp_i),
    .satp_ppn_i(satp_ppn),
    .satp_mode_i(satp_mode)
  );

  // Instantiate MMU CSRs
  mmu_csr #(
    .PADDR_WIDTH(PADDR_WIDTH)
  ) i_mmu_csr (
    .clk(clk),
    .rst_n(rst_n),
    .csr_read_en_i(csr_read_en_i),
    .csr_addr_i(csr_addr_i),
    .csr_rdata_o(csr_rdata_o),
    .csr_write_en_i(csr_write_en_i),
    .csr_addr_w_i(csr_addr_w_i),
    .csr_wdata_i(csr_wdata_i),
    .satp_ppn_o(satp_ppn),
    .satp_mode_o(satp_mode)
  );

  // MMU request handling and state machine
  typedef enum logic [1:0] {
    MMU_STATE_IDLE,
    MMU_STATE_TLB_MISS,
    MMU_STATE_PTW_WAIT
  } mmu_top_state_e;

  mmu_top_state_e mmu_state, next_mmu_state;

  logic [VADDR_WIDTH-1:0] current_vaddr;
  mmu_request_t           current_mmu_req;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      mmu_state <= MMU_STATE_IDLE;
      current_vaddr <= '0;
      current_mmu_req <= '0;
    end else begin
      mmu_state <= next_mmu_state;
      if (mmu_req_valid_i && mmu_req_ready_o) begin
        current_vaddr <= mmu_req_i.vaddr;
        current_mmu_req <= mmu_req_i;
      end
    end
  end

  always_comb begin
    next_mmu_state = mmu_state;
    mmu_req_ready_o = 1'b0;
    mmu_resp_o = '0;
    mmu_resp_valid_o = 1'b0;
    ptw_req_valid = 1'b0;
    ptw_vaddr = '0;

    case (mmu_state)
      MMU_STATE_IDLE:
        begin
          mmu_req_ready_o = tlb_req_ready; // Ready if TLB is ready
          if (mmu_req_valid_i && tlb_req_ready) begin
            if (tlb_hit) begin
              mmu_resp_o.paddr = tlb_paddr;
              mmu_resp_o.hit = 1'b1;
              mmu_resp_o.fault = tlb_fault;
              mmu_resp_o.fault_type = tlb_fault_type;
              mmu_resp_valid_o = 1'b1;
              if (mmu_resp_ready_i) begin
                next_mmu_state = MMU_STATE_IDLE;
              end
            end else begin
              // TLB Miss, request PTW
              ptw_req_valid = 1'b1;
              ptw_vaddr = mmu_req_i.vaddr;
              next_mmu_state = MMU_STATE_TLB_MISS;
            end
          end
        end

      MMU_STATE_TLB_MISS:
        begin
          ptw_req_valid = 1'b1;
          ptw_vaddr = current_vaddr;
          if (ptw_req_ready) begin
            next_mmu_state = MMU_STATE_PTW_WAIT;
          end
        end

      MMU_STATE_PTW_WAIT:
        begin
          if (ptw_done) begin
            mmu_resp_o.paddr = ptw_paddr;
            mmu_resp_o.hit = 1'b0; // It was a TLB miss
            mmu_resp_o.fault = ptw_fault;
            mmu_resp_o.fault_type = ptw_fault_type;
            mmu_resp_valid_o = 1'b1;
            if (mmu_resp_ready_i) begin
              next_mmu_state = MMU_STATE_IDLE;
            end
          end
        end

      default:
        next_mmu_state = MMU_STATE_IDLE;
    endcase
  end

endmodule
