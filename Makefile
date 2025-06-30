#=============================================================================
# RISC-V RV32IM Core - Comprehensive Verification Makefile
# Company: Sondrel Ltd
# Author: DesignAI (designai@sondrel.com)
# Created: 2025-01-27
#
# Description:
#   Makefile for building and running RISC-V core verification infrastructure.
#   Supports multiple simulation tools and provides organized test execution.
#=============================================================================

# Configuration
PROJECT_NAME = riscv_rv32im_core
TOP_DIR = $(PWD)
RTL_DIR = $(TOP_DIR)/rtl
TB_DIR = $(TOP_DIR)/tb
SIM_DIR = $(TOP_DIR)/sim
SCRIPTS_DIR = $(TOP_DIR)/scripts

# Tool Selection (Default: VCS, can override with TOOL=modelsim)
TOOL ?= vcs
SIMULATOR = $(TOOL)

# Simulator-specific settings
ifeq ($(TOOL),vcs)
    COMP = vcs
    COMP_FLAGS = +define+VCS +define+SIMULATION -sverilog -timescale=1ns/1ps \
                 +lint=TFIPC-L +warn=all -debug_access+all -kdb -lca
    SIM_FLAGS = -ucli -do $(SCRIPTS_DIR)/vcs_run.tcl
    WAVES_FLAGS = +vpd+vcdpluson
    COVERAGE_FLAGS = -cm line+cond+fsm+branch+tgl
endif

ifeq ($(TOOL),modelsim)
    COMP = vlog
    COMP_FLAGS = +define+MODELSIM +define+SIMULATION -sv -timescale 1ns/1ps
    SIM_FLAGS = -do $(SCRIPTS_DIR)/modelsim_run.tcl
    WAVES_FLAGS = +wave
    COVERAGE_FLAGS = +cover
endif

ifeq ($(TOOL),xcelium)
    COMP = xmvlog
    COMP_FLAGS = +define+XCELIUM +define+SIMULATION -sv -timescale 1ns/1ps
    SIM_FLAGS = -input $(SCRIPTS_DIR)/xcelium_run.tcl
    WAVES_FLAGS = +shm
    COVERAGE_FLAGS = -coverage all
endif

# Common RTL source files (order matters for dependencies)
RTL_PKG_FILES = \
    $(RTL_DIR)/core/riscv_config_pkg.sv \
    $(RTL_DIR)/core/riscv_exception_pkg.sv \
    $(RTL_DIR)/core/riscv_types_pkg.sv \
    $(RTL_DIR)/core/riscv_core_pkg.sv \
    $(RTL_DIR)/core/riscv_mem_types_pkg.sv \
    $(RTL_DIR)/core/riscv_ooo_types_pkg.sv \
    $(RTL_DIR)/core/riscv_protocol_types_pkg.sv \
    $(RTL_DIR)/core/riscv_cache_types_pkg.sv \
    $(RTL_DIR)/core/riscv_bp_types_pkg.sv \
    $(RTL_DIR)/core/riscv_qos_pkg.sv \
    $(RTL_DIR)/core/riscv_inter_core_types_pkg.sv \
    $(RTL_DIR)/core/riscv_protocol_constants_pkg.sv \
    $(RTL_DIR)/core/riscv_verif_types_pkg.sv

RTL_IF_FILES = \
    $(RTL_DIR)/memory/memory_req_rsp_if.sv \
    $(RTL_DIR)/interfaces/axi4_if.sv \
    $(RTL_DIR)/interfaces/chi_if.sv \
    $(RTL_DIR)/interfaces/tilelink_if.sv \
    $(RTL_DIR)/interfaces/cache_coherency_if.sv \
    $(RTL_DIR)/interfaces/inter_core_comm_if.sv \
    $(RTL_DIR)/interfaces/sync_primitives_if.sv

RTL_UNIT_FILES = \
    $(RTL_DIR)/units/alu.sv \
    $(RTL_DIR)/units/reg_file.sv \
    $(RTL_DIR)/units/mult_unit.sv \
    $(RTL_DIR)/units/div_unit.sv \
    $(RTL_DIR)/units/csr_regfile.sv \
    $(RTL_DIR)/units/exception_handler.sv \
    $(RTL_DIR)/units/qos_exception_handler.sv

RTL_CORE_FILES = \
    $(RTL_DIR)/core/fetch_stage.sv \
    $(RTL_DIR)/core/decode_stage.sv \
    $(RTL_DIR)/core/execute_stage.sv \
    $(RTL_DIR)/core/mem_stage.sv \
    $(RTL_DIR)/core/writeback_stage.sv \
    $(RTL_DIR)/core/core_subsystem.sv \
    $(RTL_DIR)/core/core_manager.sv \
    $(RTL_DIR)/core/riscv_core.sv

RTL_MEMORY_FILES = \
    $(RTL_DIR)/memory/icache.sv \
    $(RTL_DIR)/memory/l2_cache.sv \
    $(RTL_DIR)/memory/l3_cache.sv \
    $(RTL_DIR)/memory/memory_wrapper.sv \
    $(RTL_DIR)/memory/qos_memory_wrapper.sv \
    $(RTL_DIR)/memory/cache_coherency_controller.sv \
    $(RTL_DIR)/memory/prefetch_unit.sv \
    $(RTL_DIR)/memory/matrix_lru.sv \
    $(RTL_DIR)/memory/qos_aware_cache.sv

RTL_EXECUTION_FILES = \
    $(RTL_DIR)/execution/reorder_buffer.sv \
    $(RTL_DIR)/execution/reservation_station.sv \
    $(RTL_DIR)/execution/register_renaming.sv \
    $(RTL_DIR)/execution/multiple_execution_units.sv

RTL_PROTOCOL_FILES = \
    $(RTL_DIR)/protocols/axi4_adapter.sv \
    $(RTL_DIR)/protocols/chi_adapter.sv \
    $(RTL_DIR)/protocols/tilelink_adapter.sv \
    $(RTL_DIR)/protocols/protocol_factory.sv \
    $(RTL_DIR)/protocols/qos_arbiter.sv

RTL_PREDICTION_FILES = \
    $(RTL_DIR)/prediction/branch_predictor.sv \
    $(RTL_DIR)/prediction/return_stack_buffer.sv \
    $(RTL_DIR)/prediction/tournament_predictor.sv

RTL_POWER_FILES = \
    $(RTL_DIR)/power/power_management.sv

RTL_CONTROL_FILES = \
    $(RTL_DIR)/control/hazard_unit.sv

RTL_SYSTEM_FILES = \
    $(RTL_DIR)/core/multi_core_system.sv \
    $(RTL_DIR)/core/ooo_engine.sv \
    $(RTL_DIR)/core/qos_csr_regfile.sv

# All RTL files in dependency order
ALL_RTL_FILES = $(RTL_PKG_FILES) $(RTL_IF_FILES) $(RTL_UNIT_FILES) \
                $(RTL_CORE_FILES) $(RTL_MEMORY_FILES) $(RTL_EXECUTION_FILES) \
                $(RTL_PROTOCOL_FILES) $(RTL_PREDICTION_FILES) $(RTL_POWER_FILES) \
                $(RTL_CONTROL_FILES) $(RTL_SYSTEM_FILES)

# Common testbench files
TB_COMMON_FILES = \
    $(TB_DIR)/common/test_utils.sv \
    $(TB_DIR)/common/assertions.sv \
    $(TB_DIR)/common/test_env.sv

# Specific testbench definitions
ALU_TB_FILES = $(RTL_PKG_FILES) $(RTL_DIR)/units/alu.sv $(TB_DIR)/unit/units/alu_tb.sv
REG_FILE_TB_FILES = $(RTL_PKG_FILES) $(RTL_DIR)/units/reg_file.sv $(TB_DIR)/unit/units/reg_file_tb.sv
CORE_INTEGRATION_TB_FILES = $(ALL_RTL_FILES) $(TB_DIR)/integration/riscv_core_integration_tb.sv

# Simulation directories
SIM_ALU_DIR = $(SIM_DIR)/alu
SIM_REG_FILE_DIR = $(SIM_DIR)/reg_file  
SIM_CORE_DIR = $(SIM_DIR)/core_integration
SIM_MULTI_CORE_DIR = $(SIM_DIR)/multi_core

# Default target
.PHONY: all
all: help

# Help target
.PHONY: help
help:
	@echo "================================================================="
	@echo "RISC-V RV32IM Core Verification Makefile"
	@echo "================================================================="
	@echo "Available targets:"
	@echo ""
	@echo "Unit Tests:"
	@echo "  alu                 - Run ALU unit test"
	@echo "  reg_file           - Run Register File unit test"
	@echo "  units              - Run all unit tests"
	@echo ""
	@echo "Integration Tests:"
	@echo "  core_integration   - Run core integration test"
	@echo "  integration        - Run all integration tests"
	@echo ""
	@echo "Utility:"
	@echo "  clean              - Clean simulation files"
	@echo "  compile_check      - Check RTL compilation"
	@echo "  lint               - Run static analysis"
	@echo "  coverage_report    - Generate coverage report"
	@echo ""
	@echo "Configuration:"
	@echo "  TOOL=vcs|modelsim|xcelium (default: vcs)"
	@echo "  WAVES=1            - Enable waveform generation"
	@echo "  COVERAGE=1         - Enable coverage collection"
	@echo "  SEED=<num>         - Set random seed"
	@echo "  VERBOSITY=<level>  - Set verbosity level"
	@echo ""
	@echo "Examples:"
	@echo "  make alu TOOL=vcs WAVES=1"
	@echo "  make units COVERAGE=1"
	@echo "  make core_integration WAVES=1 VERBOSITY=3"
	@echo "================================================================="

# Create simulation directories
$(SIM_ALU_DIR) $(SIM_REG_FILE_DIR) $(SIM_CORE_DIR) $(SIM_MULTI_CORE_DIR):
	@mkdir -p $@

# Optional flags based on environment variables
ifdef WAVES
    COMP_FLAGS += $(WAVES_FLAGS)
    SIM_FLAGS += +WAVES=1
endif

ifdef COVERAGE
    COMP_FLAGS += $(COVERAGE_FLAGS)
    SIM_FLAGS += +COVERAGE=1
endif

ifdef SEED
    SIM_FLAGS += +SEED=$(SEED)
else
    SIM_FLAGS += +SEED=1
endif

ifdef VERBOSITY
    SIM_FLAGS += +VERBOSITY=$(VERBOSITY)
else
    SIM_FLAGS += +VERBOSITY=1
endif

#=============================================================================
# Unit Tests
#=============================================================================

.PHONY: alu
alu: $(SIM_ALU_DIR)
	@echo "================================================================="
	@echo "Running ALU Unit Test"
	@echo "================================================================="
	cd $(SIM_ALU_DIR) && \
	$(COMP) $(COMP_FLAGS) +incdir+$(RTL_DIR)/core +incdir+$(TB_DIR)/common \
	    $(ALU_TB_FILES) -top alu_tb -o alu_tb_sim && \
	./alu_tb_sim $(SIM_FLAGS) +TEST_NAME=alu_unit_test
	@echo "ALU test completed. Check $(SIM_ALU_DIR) for results."

.PHONY: reg_file
reg_file: $(SIM_REG_FILE_DIR)
	@echo "================================================================="
	@echo "Running Register File Unit Test"
	@echo "================================================================="
	cd $(SIM_REG_FILE_DIR) && \
	$(COMP) $(COMP_FLAGS) +incdir+$(RTL_DIR)/core +incdir+$(TB_DIR)/common \
	    $(REG_FILE_TB_FILES) -top reg_file_tb -o reg_file_tb_sim && \
	./reg_file_tb_sim $(SIM_FLAGS) +TEST_NAME=reg_file_unit_test
	@echo "Register File test completed. Check $(SIM_REG_FILE_DIR) for results."

.PHONY: units
units: alu reg_file
	@echo "================================================================="
	@echo "All Unit Tests Completed"
	@echo "================================================================="
	@echo "Results:"
	@echo "  ALU Test:       $(SIM_ALU_DIR)"
	@echo "  Register File:  $(SIM_REG_FILE_DIR)"

#=============================================================================
# Integration Tests
#=============================================================================

.PHONY: core_integration
core_integration: $(SIM_CORE_DIR)
	@echo "================================================================="
	@echo "Running Core Integration Test"
	@echo "================================================================="
	cd $(SIM_CORE_DIR) && \
	$(COMP) $(COMP_FLAGS) +incdir+$(RTL_DIR)/core +incdir+$(TB_DIR)/common \
	    $(CORE_INTEGRATION_TB_FILES) -top riscv_core_integration_tb \
	    -o core_integration_tb_sim && \
	./core_integration_tb_sim $(SIM_FLAGS) +TEST_NAME=core_integration_test
	@echo "Core integration test completed. Check $(SIM_CORE_DIR) for results."

.PHONY: integration
integration: core_integration
	@echo "================================================================="
	@echo "All Integration Tests Completed"
	@echo "================================================================="

#=============================================================================
# Utility Targets
#=============================================================================

.PHONY: compile_check
compile_check:
	@echo "================================================================="
	@echo "Checking RTL Compilation"
	@echo "================================================================="
	@mkdir -p $(SIM_DIR)/compile_check
	cd $(SIM_DIR)/compile_check && \
	$(COMP) $(COMP_FLAGS) +incdir+$(RTL_DIR)/core \
	    $(ALL_RTL_FILES) -top multi_core_system -o compile_check
	@echo "Compilation check completed successfully."

.PHONY: lint
lint:
	@echo "================================================================="
	@echo "Running Static Analysis"
	@echo "================================================================="
	@if command -v verilator >/dev/null 2>&1; then \
	    echo "Running Verilator lint..."; \
	    verilator --lint-only --top-module riscv_core \
	        +incdir+$(RTL_DIR)/core $(ALL_RTL_FILES); \
	else \
	    echo "Verilator not found. Skipping lint check."; \
	fi

.PHONY: coverage_report
coverage_report:
	@echo "================================================================="
	@echo "Generating Coverage Report"
	@echo "================================================================="
	@if [ -d "$(SIM_DIR)" ]; then \
	    find $(SIM_DIR) -name "*.vdb" -o -name "cov.db" | head -1 | \
	    xargs -I {} echo "Coverage database found: {}"; \
	    echo "Use your simulator's coverage tools to generate reports."; \
	else \
	    echo "No coverage databases found. Run tests with COVERAGE=1"; \
	fi

.PHONY: clean
clean:
	@echo "Cleaning simulation files..."
	rm -rf $(SIM_DIR)
	rm -rf simv* csrc *.daidir *.log *.vpd *.fsdb *.vcd
	rm -rf urgReport* *.history transcript* work* modelsim.ini
	rm -rf xcelium.d *.shm *.trn *.dsn
	rm -rf phase1_results
	@echo "Clean completed."

#=============================================================================
# Advanced Targets
#=============================================================================

.PHONY: regression
regression: units integration
	@echo "================================================================="
	@echo "REGRESSION TEST COMPLETED"
	@echo "================================================================="
	@echo "All tests have been executed. Check individual directories for results."

.PHONY: debug_alu
debug_alu: WAVES = 1
debug_alu: VERBOSITY = 3
debug_alu: alu

.PHONY: debug_core
debug_core: WAVES = 1
debug_core: VERBOSITY = 3
debug_core: core_integration

.PHONY: quick_check
quick_check:
	@echo "Running quick compilation and basic unit tests..."
	@$(MAKE) compile_check --no-print-directory
	@$(MAKE) alu VERBOSITY=1 --no-print-directory
	@echo "Quick check completed."

#=============================================================================
# Parallel execution (if supported)
#=============================================================================

.PHONY: parallel_units
parallel_units:
	@echo "Running unit tests in parallel..."
	@$(MAKE) -j2 alu reg_file

#=============================================================================
# Help for specific tools
#=============================================================================

.PHONY: help_vcs
help_vcs:
	@echo "VCS-specific options:"
	@echo "  +define+VCS        - VCS-specific defines"
	@echo "  -debug_access+all  - Enable debugging"
	@echo "  -kdb              - Enable KDB debugging"
	@echo "  +vpd+vcdpluson    - Enable VPD waveforms"

.PHONY: help_modelsim
help_modelsim:
	@echo "ModelSim-specific options:"
	@echo "  +define+MODELSIM  - ModelSim-specific defines"
	@echo "  +wave            - Enable waveforms"
	@echo "  +cover           - Enable coverage"

#=============================================================================
# File dependencies (for make to track changes)
#=============================================================================

$(SIM_ALU_DIR)/alu_tb_sim: $(ALU_TB_FILES) | $(SIM_ALU_DIR)
$(SIM_REG_FILE_DIR)/reg_file_tb_sim: $(REG_FILE_TB_FILES) | $(SIM_REG_FILE_DIR)
$(SIM_CORE_DIR)/core_integration_tb_sim: $(CORE_INTEGRATION_TB_FILES) | $(SIM_CORE_DIR)

#=============================================================================
# Variables for debugging
#=============================================================================

.PHONY: show_vars
show_vars:
	@echo "Makefile Variables:"
	@echo "  TOOL = $(TOOL)"
	@echo "  COMP = $(COMP)"
	@echo "  COMP_FLAGS = $(COMP_FLAGS)"
	@echo "  SIM_FLAGS = $(SIM_FLAGS)"
	@echo "  RTL_DIR = $(RTL_DIR)"
	@echo "  TB_DIR = $(TB_DIR)"
	@echo "  SIM_DIR = $(SIM_DIR)"

#=============================================================================
# End of Makefile
# 
# Usage Examples:
#   make alu                    # Run ALU test with VCS
#   make reg_file TOOL=modelsim # Run Register File test with ModelSim
#   make units WAVES=1          # Run all unit tests with waveforms
#   make core_integration COVERAGE=1 # Run integration test with coverage
#   make regression             # Run full regression suite
#   make clean                  # Clean all simulation files
#============================================================================= 