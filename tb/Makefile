#=============================================================================
# RISC-V Testbench Makefile
#=============================================================================
# Company: Sondrel Ltd
# Author: DesignAI (designai@sondrel.com)
# Created: 2025-07-05
#
# Description:
#   Makefile for compiling and running RISC-V unit testbenches.
#   Supports VCS and ModelSim simulators.
#=============================================================================

#===========================================================================
# Configuration
#===========================================================================
PROJECT_ROOT := $(shell pwd)/..
SIMULATOR ?= vcs
VCS_FLAGS := -full64 -sverilog -debug_all +v2k +define+SIMULATION
MODELSIM_FLAGS := -sv

#===========================================================================
# Directories
#===========================================================================
TB_DIR := $(PROJECT_ROOT)/tb
RTL_DIR := $(PROJECT_ROOT)/rtl
UNIT_DIR := $(TB_DIR)/unit
COMMON_DIR := $(TB_DIR)/common

#===========================================================================
# Common Files
#===========================================================================
COMMON_FILES := $(COMMON_DIR)/test_utils.sv
RTL_PKG := $(RTL_DIR)/core/riscv_core_pkg.sv

#===========================================================================
# Find all testbenches
#===========================================================================
TESTBENCHES := $(shell find $(UNIT_DIR) -name "*_tb.sv" -type f)
TESTBENCH_NAMES := $(notdir $(basename $(TESTBENCHES)))

#===========================================================================
# Default target
#===========================================================================
.PHONY: all clean help
all: compile run

help:
	@echo "RISC-V Testbench Makefile"
	@echo "========================="
	@echo ""
	@echo "Available targets:"
	@echo "  all          - Compile and run all tests"
	@echo "  compile      - Compile all testbenches"
	@echo "  run          - Run all compiled testbenches"
	@echo "  clean        - Clean all generated files"
	@echo "  help         - Show this help message"
	@echo ""
	@echo "Test-specific targets:"
	@echo "  alu_test     - Compile and run ALU test"
	@echo "  reg_test     - Compile and run Register File test"
	@echo "  mult_test    - Compile and run Multiplier test"
	@echo "  div_test     - Compile and run Divider test"
	@echo "  csr_test     - Compile and run CSR test"
	@echo "  hazard_test  - Compile and run Hazard Unit test"
	@echo "  icache_test  - Compile and run ICache test"
	@echo "  mem_test     - Compile and run Memory Wrapper test"
	@echo "  axi_test     - Compile and run AXI4 Adapter test"
	@echo "  bp_test      - Compile and run Branch Predictor test
  fpu_test     - Compile and run FPU test
  vpu_test     - Compile and run VPU test
  mliu_test    - Compile and run MLIU test"
	@echo ""
	@echo "Variables:"
	@echo "  SIMULATOR    - Simulator to use (vcs/modelsim, default: vcs)"
	@echo "  VCS_FLAGS    - VCS compilation flags"
	@echo "  MODELSIM_FLAGS - ModelSim compilation flags"

#===========================================================================
# Compilation targets
#===========================================================================
.PHONY: compile
compile: $(addprefix compile_, $(TESTBENCH_NAMES))

# ALU Test
compile_alu_tb: $(UNIT_DIR)/units/alu_tb.sv
	@echo "Compiling ALU testbench..."
	@cd $(UNIT_DIR)/units && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/alu_tb.f \
		-o alu_tb

# Register File Test
compile_reg_file_tb: $(UNIT_DIR)/units/reg_file_tb.sv
	@echo "Compiling Register File testbench..."
	@cd $(UNIT_DIR)/units && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/reg_file_tb.f \
		-o reg_file_tb

# Multiplier Test
compile_mult_unit_tb: $(UNIT_DIR)/units/mult_unit_tb.sv
	@echo "Compiling Multiplier testbench..."
	@cd $(UNIT_DIR)/units && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/mult_unit_tb.f \
		-o mult_unit_tb

# Divider Test
compile_div_unit_tb: $(UNIT_DIR)/units/div_unit_tb.sv
	@echo "Compiling Divider testbench..."
	@cd $(UNIT_DIR)/units && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/div_unit_tb.f \
		-o div_unit_tb

# CSR Register File Test
compile_csr_regfile_tb: $(UNIT_DIR)/units/csr_regfile_tb.sv
	@echo "Compiling CSR Register File testbench..."
	@cd $(UNIT_DIR)/units && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/csr_regfile_tb.f \
		-o csr_regfile_tb

# Exception Handler Test
compile_exception_handler_tb: $(UNIT_DIR)/units/exception_handler_tb.sv
	@echo "Compiling Exception Handler testbench..."
	@cd $(UNIT_DIR)/units && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/exception_handler_tb.f \
		-o exception_handler_tb

# Hazard Unit Test
compile_hazard_unit_tb: $(UNIT_DIR)/control/hazard_unit_tb.sv
	@echo "Compiling Hazard Unit testbench..."
	@cd $(UNIT_DIR)/control && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/hazard_unit_tb.f \
		-o hazard_unit_tb

# ICache Test
compile_icache_tb: $(UNIT_DIR)/memory/icache_tb.sv
	@echo "Compiling ICache testbench..."
	@cd $(UNIT_DIR)/memory && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/icache_tb.f \
		-o icache_tb

# Memory Wrapper Test
compile_memory_wrapper_tb: $(UNIT_DIR)/memory/memory_wrapper_tb.sv
	@echo "Compiling Memory Wrapper testbench..."
	@cd $(UNIT_DIR)/memory && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/memory_wrapper_tb.f \
		-o memory_wrapper_tb

# AXI4 Adapter Test
compile_axi4_adapter_tb: $(UNIT_DIR)/protocols/axi4_adapter_tb.sv
	@echo "Compiling AXI4 Adapter testbench..."
	@cd $(UNIT_DIR)/protocols && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/axi4_adapter_tb.f \
		-o axi4_adapter_tb

# Branch Predictor Test
compile_branch_predictor_tb: $(UNIT_DIR)/prediction/branch_predictor_tb.sv
	@echo "Compiling Branch Predictor testbench..."
	@cd $(UNIT_DIR)/prediction && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/branch_predictor_tb.f \
		-o branch_predictor_tb

# FPU Test
compile_fpu_tb: $(UNIT_DIR)/units/fpu_tb.sv
	@echo "Compiling FPU testbench..."
	@cd $(UNIT_DIR)/units && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/fpu_tb.f \
		-o fpu_tb

# VPU Test
compile_vpu_tb: $(UNIT_DIR)/units/vpu_tb.sv
	@echo "Compiling VPU testbench..."
	@cd $(UNIT_DIR)/units && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/vpu_tb.f \
		-o vpu_tb

# MLIU Test
compile_mliu_tb: $(UNIT_DIR)/units/mliu_tb.sv
	@echo "Compiling MLIU testbench..."
	@cd $(UNIT_DIR)/units && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/mliu_tb.f \
		-o mliu_tb

# Decode Stage Test
compile_decode_stage_tb: $(UNIT_DIR)/decode_stage_tb.sv
	@echo "Compiling Decode Stage testbench..."
	@cd $(UNIT_DIR) && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/decode_stage_tb.f \
		-o decode_stage_tb



# Memory Stage Test
compile_mem_stage_tb: $(UNIT_DIR)/mem_stage_tb.sv
	@echo "Compiling Memory Stage testbench..."
	@cd $(UNIT_DIR) && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/mem_stage_tb.f \
		-o mem_stage_tb

# Writeback Stage Test
compile_writeback_stage_tb: $(UNIT_DIR)/writeback_stage_tb.sv
	@echo "Compiling Writeback Stage testbench..."
	@cd $(UNIT_DIR) && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/writeback_stage_tb.f \
		-o writeback_stage_tb

# Writeback Stage Test
compile_writeback_stage_tb: $(UNIT_DIR)/writeback_stage_tb.sv
	@echo "Compiling Writeback Stage testbench..."
	@cd $(UNIT_DIR) && \
	$(SIMULATOR) $(VCS_FLAGS) \
		-f $(TB_DIR)/filelists/writeback_stage_tb.f \
		-o writeback_stage_tb

#===========================================================================
# Execution targets
#===========================================================================
.PHONY: run
run: $(addprefix run_, $(TESTBENCH_NAMES))

# ALU Test
run_alu_tb: compile_alu_tb
	@echo "Running ALU testbench..."
	@cd $(UNIT_DIR)/units && ./alu_tb

# Register File Test
run_reg_file_tb: compile_reg_file_tb
	@echo "Running Register File testbench..."
	@cd $(UNIT_DIR)/units && ./reg_file_tb

# Multiplier Test
run_mult_unit_tb: compile_mult_unit_tb
	@echo "Running Multiplier testbench..."
	@cd $(UNIT_DIR)/units && ./mult_unit_tb

# Divider Test
run_div_unit_tb: compile_div_unit_tb
	@echo "Running Divider testbench..."
	@cd $(UNIT_DIR)/units && ./div_unit_tb

# CSR Register File Test
run_csr_regfile_tb: compile_csr_regfile_tb
	@echo "Running CSR Register File testbench..."
	@cd $(UNIT_DIR)/units && ./csr_regfile_tb

# Exception Handler Test
run_exception_handler_tb: compile_exception_handler_tb
	@echo "Running Exception Handler testbench..."
	@cd $(UNIT_DIR)/units && ./exception_handler_tb

# Hazard Unit Test
run_hazard_unit_tb: compile_hazard_unit_tb
	@echo "Running Hazard Unit testbench..."
	@cd $(UNIT_DIR)/control && ./hazard_unit_tb

# ICache Test
run_icache_tb: compile_icache_tb
	@echo "Running ICache testbench..."
	@cd $(UNIT_DIR)/memory && ./icache_tb

# Memory Wrapper Test
run_memory_wrapper_tb: compile_memory_wrapper_tb
	@echo "Running Memory Wrapper testbench..."
	@cd $(UNIT_DIR)/memory && ./memory_wrapper_tb

# AXI4 Adapter Test
run_axi4_adapter_tb: compile_axi4_adapter_tb
	@echo "Running AXI4 Adapter testbench..."
	@cd $(UNIT_DIR)/protocols && ./axi4_adapter_tb

# Branch Predictor Test
run_branch_predictor_tb: compile_branch_predictor_tb
	@echo "Running Branch Predictor testbench..."
	@cd $(UNIT_DIR)/prediction && ./branch_predictor_tb

# FPU Test
run_fpu_tb: compile_fpu_tb
	@echo "Running FPU testbench..."
	@cd $(UNIT_DIR)/units && ./fpu_tb

# VPU Test
run_vpu_tb: compile_vpu_tb
	@echo "Running VPU testbench..."
	@cd $(UNIT_DIR)/units && ./vpu_tb

# MLIU Test
run_mliu_tb: compile_mliu_tb
	@echo "Running MLIU testbench..."
	@cd $(UNIT_DIR)/units && ./mliu_tb

#===========================================================================
# Individual test targets
#===========================================================================
.PHONY: alu_test reg_test mult_test div_test csr_test hazard_test icache_test mem_test axi_test bp_test

alu_test: run_alu_tb
reg_test: run_reg_file_tb
mult_test: run_mult_unit_tb
div_test: run_div_unit_tb
csr_test: run_csr_regfile_tb
hazard_test: run_hazard_unit_tb
icache_test: run_icache_tb
mem_test: run_memory_wrapper_tb
axi_test: run_axi4_adapter_tb
bp_test: run_branch_predictor_tb
fpu_test: run_fpu_tb
vpu_test: run_vpu_tb
mliu_test: run_mliu_tb

#===========================================================================
# Clean target
#===========================================================================
.PHONY: clean
clean:
	@echo "Cleaning generated files..."
	@find $(TB_DIR) -name "*.f" -delete
	@find $(TB_DIR) -name "simv*" -delete
	@find $(TB_DIR) -name "*.log" -delete
	@find $(TB_DIR) -name "*.vpd" -delete
	@find $(TB_DIR) -name "*.vdb" -delete
	@find $(TB_DIR) -name "*.key" -delete
	@find $(TB_DIR) -name "*.so" -delete
	@find $(TB_DIR) -name "*.o" -delete
	@find $(TB_DIR) -name "*.daidir" -type d -exec rm -rf {} + 2>/dev/null || true
	@find $(TB_DIR) -name "csrc" -type d -exec rm -rf {} + 2>/dev/null || true
	@find $(TB_DIR) -name "work" -type d -exec rm -rf {} + 2>/dev/null || true
	@find $(TB_DIR) -name "transcript" -delete
	@find $(TB_DIR) -name "*.wlf" -delete
	@find $(TB_DIR) -name "*.vstf" -delete
	@find $(TB_DIR) -name "*.ucdb" -delete
	@find $(TB_DIR) -name "*.acdb" -delete
	@find $(TB_DIR) -name "*.rc" -delete
	@find $(TB_DIR) -name "*.ini" -delete
	@find $(TB_DIR) -name "*.bak" -delete
	@find $(TB_DIR) -name "*.tmp" -delete
	@echo "Clean complete."

#===========================================================================
# Filelist generation
#===========================================================================
.PHONY: filelists
filelists:
	@echo "Generating filelists..."
	@mkdir -p $(TB_DIR)/filelists
	
	# ALU testbench filelist
	@echo "$(COMMON_FILES)" > $(TB_DIR)/filelists/alu_tb.f
	@echo "$(RTL_PKG)" >> $(TB_DIR)/filelists/alu_tb.f
	@echo "$(RTL_DIR)/units/alu.sv" >> $(TB_DIR)/filelists/alu_tb.f
	@echo "$(UNIT_DIR)/units/alu_tb.sv" >> $(TB_DIR)/filelists/alu_tb.f
	
	# Register File testbench filelist
	@echo "$(COMMON_FILES)" > $(TB_DIR)/filelists/reg_file_tb.f
	@echo "$(RTL_PKG)" >> $(TB_DIR)/filelists/reg_file_tb.f
	@echo "$(RTL_DIR)/units/reg_file.sv" >> $(TB_DIR)/filelists/reg_file_tb.f
	@echo "$(UNIT_DIR)/units/reg_file_tb.sv" >> $(TB_DIR)/filelists/reg_file_tb.f
	
	# Add more filelists as needed...
	# FPU testbench filelist
	@echo "$(COMMON_FILES)" > $(TB_DIR)/filelists/fpu_tb.f
	@echo "$(RTL_PKG)" >> $(TB_DIR)/filelists/fpu_tb.f
	@echo "$(RTL_DIR)/core/fpu_unit.sv" >> $(TB_DIR)/filelists/fpu_tb.f
	@echo "$(UNIT_DIR)/units/fpu_tb.sv" >> $(TB_DIR)/filelists/fpu_tb.f
	@echo "$(RTL_DIR)/core/riscv_fpu_types_pkg.sv" >> $(TB_DIR)/filelists/fpu_tb.f

	# VPU testbench filelist
	@echo "$(COMMON_FILES)" > $(TB_DIR)/filelists/vpu_tb.f
	@echo "$(RTL_PKG)" >> $(TB_DIR)/filelists/vpu_tb.f
	@echo "$(RTL_DIR)/core/vpu_unit.sv" >> $(TB_DIR)/filelists/vpu_tb.f
	@echo "$(UNIT_DIR)/units/vpu_tb.sv" >> $(TB_DIR)/filelists/vpu_tb.f
	@echo "$(RTL_DIR)/core/riscv_vpu_types_pkg.sv" >> $(TB_DIR)/filelists/vpu_tb.f

	# MLIU testbench filelist
	@echo "$(COMMON_FILES)" > $(TB_DIR)/filelists/mliu_tb.f
	@echo "$(RTL_PKG)" >> $(TB_DIR)/filelists/mliu_tb.f
	@echo "$(RTL_DIR)/core/ml_inference_unit.sv" >> $(TB_DIR)/filelists/mliu_tb.f
	@echo "$(UNIT_DIR)/units/mliu_tb.sv" >> $(TB_DIR)/filelists/mliu_tb.f
	@echo "$(RTL_DIR)/core/riscv_ml_types_pkg.sv" >> $(TB_DIR)/filelists/mliu_tb.f

	@echo "Filelists generated."

#===========================================================================
# Coverage targets
#===========================================================================
.PHONY: coverage
coverage: compile
	@echo "Running tests with coverage..."
	@$(MAKE) run VCS_FLAGS="$(VCS_FLAGS) -cm line+cond+fsm+branch+tgl"

#===========================================================================
# Debug targets
#===========================================================================
.PHONY: debug
debug: compile
	@echo "Running tests in debug mode..."
	@$(MAKE) run VCS_FLAGS="$(VCS_FLAGS) -debug_all"

#===========================================================================
# Dependencies
#===========================================================================
$(UNIT_DIR)/units/alu_tb.sv: $(COMMON_FILES) $(RTL_PKG) $(RTL_DIR)/units/alu.sv
$(UNIT_DIR)/units/reg_file_tb.sv: $(COMMON_FILES) $(RTL_PKG) $(RTL_DIR)/units/reg_file.sv
$(UNIT_DIR)/units/mult_unit_tb.sv: $(COMMON_FILES) $(RTL_PKG) $(RTL_DIR)/units/mult_unit.sv
$(UNIT_DIR)/units/div_unit_tb.sv: $(COMMON_FILES) $(RTL_PKG) $(RTL_DIR)/units/div_unit.sv
$(UNIT_DIR)/units/csr_regfile_tb.sv: $(COMMON_FILES) $(RTL_PKG) $(RTL_DIR)/units/csr_regfile.sv
$(UNIT_DIR)/units/exception_handler_tb.sv: $(COMMON_FILES) $(RTL_PKG) $(RTL_DIR)/units/exception_handler.sv
$(UNIT_DIR)/control/hazard_unit_tb.sv: $(COMMON_FILES) $(RTL_PKG) $(RTL_DIR)/control/hazard_unit.sv
$(UNIT_DIR)/memory/icache_tb.sv: $(COMMON_FILES) $(RTL_PKG) $(RTL_DIR)/memory/icache.sv
$(UNIT_DIR)/memory/memory_wrapper_tb.sv: $(COMMON_FILES) $(RTL_PKG) $(RTL_DIR)/memory/memory_wrapper.sv
$(UNIT_DIR)/protocols/axi4_adapter_tb.sv: $(COMMON_FILES) $(RTL_PKG) $(RTL_DIR)/protocols/axi4_adapter.sv
$(UNIT_DIR)/prediction/branch_predictor_tb.sv: $(COMMON_FILES) $(RTL_PKG) $(RTL_DIR)/prediction/branch_predictor.sv
$(UNIT_DIR)/units/fpu_tb.sv: $(COMMON_FILES) $(RTL_PKG) $(RTL_DIR)/core/fpu_unit.sv $(RTL_DIR)/core/riscv_fpu_types_pkg.sv
$(UNIT_DIR)/units/vpu_tb.sv: $(COMMON_FILES) $(RTL_PKG) $(RTL_DIR)/core/vpu_unit.sv $(RTL_DIR)/core/riscv_vpu_types_pkg.sv
$(UNIT_DIR)/units/mliu_tb.sv: $(COMMON_FILES) $(RTL_PKG) $(RTL_DIR)/core/ml_inference_unit.sv $(RTL_DIR)/core/riscv_ml_types_pkg.sv
$(UNIT_DIR)/writeback_stage_tb.sv: $(COMMON_FILES) $(RTL_PKG) $(RTL_DIR)/core/riscv_config_pkg.sv $(RTL_DIR)/core/writeback_stage.sv 