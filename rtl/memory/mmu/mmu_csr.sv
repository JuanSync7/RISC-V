`timescale 1ns / 1ps

import mmu_pkg::*;

module mmu_csr #(
  parameter int PADDR_WIDTH = MMU_PADDR_WIDTH
) (
  input  logic        clk,
  input  logic        rst_n,

  // CSR read interface
  input  logic        csr_read_en_i,
  input  logic [11:0] csr_addr_i,
  output logic [31:0] csr_rdata_o,

  // CSR write interface
  input  logic        csr_write_en_i,
  input  logic [11:0] csr_addr_w_i,
  input  logic [31:0] csr_wdata_i,

  // MMU specific outputs
  output logic [PADDR_WIDTH-1:0] satp_ppn_o, // Physical Page Number from satp
  output logic [3:0]              satp_mode_o // MMU mode from satp
);

  // satp register: Supervisor Address Translation and Protection Register
  // Format: MODE (31:28), ASID (27:22), PPN (21:0)
  logic [31:0] satp_reg;

  // CSR addresses (simplified for now, actual RISC-V CSR addresses are 12-bit)
  localparam SATP_CSR_ADDR = 12'h180; // Example address for satp

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      satp_reg <= '0;
    end else begin
      if (csr_write_en_i && (csr_addr_w_i == SATP_CSR_ADDR)) begin
        satp_reg <= csr_wdata_i;
      end
    end
  end

  always_comb begin
    csr_rdata_o = '0;
    if (csr_read_en_i && (csr_addr_i == SATP_CSR_ADDR)) begin
      csr_rdata_o = satp_reg;
    end

    // Extract PPN and MODE from satp_reg
    // Assuming Sv32 mode for now, PPN is bits 21:0
    satp_ppn_o = satp_reg[MMU_PPN_WIDTH-1:0];
    satp_mode_o = satp_reg[31:28];
  end

endmodule
