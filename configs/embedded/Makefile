# Generated Makefile for RISC-V embedded configuration
# Generated on 2025-07-04 21:00:38

# Configuration
CONFIG_NAME = embedded
NUM_CORES = 1
ISA = RV32IM

# Directories
RTL_DIR = ../rtl
TB_DIR = ../tb
BUILD_DIR = build_$(CONFIG_NAME)

# Source files
RTL_SOURCES = \
    $(RTL_DIR)/packages/base/riscv_base_pkg.sv \
    $(RTL_DIR)/packages/riscv_system_config_pkg.sv \
    $(RTL_DIR)/core/riscv_types_pkg.sv \
    $(RTL_DIR)/core/riscv_exception_pkg.sv \
    $(RTL_DIR)/core/riscv_core_pkg.sv \
    $(RTL_DIR)/units/alu.sv \
    $(RTL_DIR)/units/reg_file.sv \
    $(RTL_DIR)/units/csr_regfile.sv \
    $(RTL_DIR)/units/fence_unit.sv \
    $(RTL_DIR)/core/fetch_stage.sv \
    $(RTL_DIR)/core/decode_stage.sv \
    $(RTL_DIR)/core/execute_stage.sv \
    $(RTL_DIR)/core/mem_stage.sv \
    $(RTL_DIR)/core/writeback_stage.sv \
    $(RTL_DIR)/core/riscv_core.sv
    $(RTL_DIR)/peripherals/clint.sv \
    $(RTL_DIR)/peripherals/plic.sv \

# Default target
all: compile

# Create build directory
$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

# Compile with Verilator
compile_verilator: $(BUILD_DIR)
	verilator --sv --cc --exe --build \
		--top-module riscv_core \
		-I$(RTL_DIR)/packages \
		-I$(RTL_DIR)/core \
		-I$(RTL_DIR) \
		$(RTL_SOURCES) \
		-o $(BUILD_DIR)/Vriscv_core

# Compile with Icarus Verilog
compile_iverilog: $(BUILD_DIR)
	iverilog -g2012 -o $(BUILD_DIR)/riscv_core.vvp \
		-I $(RTL_DIR)/packages \
		-I $(RTL_DIR)/core \
		$(RTL_SOURCES)

# Run simulation
sim: compile_iverilog
	vvp $(BUILD_DIR)/riscv_core.vvp

# Clean build artifacts
clean:
	rm -rf $(BUILD_DIR)

.PHONY: all compile compile_verilator compile_iverilog sim clean
