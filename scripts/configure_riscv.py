#!/usr/bin/env python3
"""
RISC-V Core Configuration Management Script

This script manages different RISC-V core configurations and generates
appropriate RTL and build files for the selected profile.

Usage:
    python3 configure_riscv.py --profile <profile_name> [options]

Profiles:
    - embedded: Small, single-core RV32IM for microcontrollers
    - application: Medium, multi-core RV32IMAC for IoT/embedded Linux
    - server: Large, multi-core RV32IMAC with OoO for application processors
    - custom: User-defined configuration from JSON file
"""

import argparse
import json
import os
import sys
from pathlib import Path
from datetime import datetime
import shutil

# Configuration profiles
PROFILES = {
    "embedded": {
        "name": "Embedded Profile",
        "description": "Small RV32IM core for microcontrollers",
        "config": {
            "isa": "RV32IM",
            "num_cores": 1,
            "pipeline": "in_order",
            "cache": {
                "icache_size_kb": 4,
                "icache_ways": 2,
                "dcache_size_kb": 4,
                "dcache_ways": 2,
                "l2_cache_size_kb": 0,
                "l3_cache_size_kb": 0
            },
            "features": {
                "branch_predictor": "simple",
                "ooo_enable": False,
                "mmu_enable": False,
                "fpu_enable": False,
                "atomic_enable": False,
                "compressed_enable": False,
                "vector_enable": False
            },
            "peripherals": {
                "clint": True,
                "plic": True,
                "uart": True,
                "gpio": True,
                "spi": False,
                "i2c": False
            },
            "memory": {
                "ram_size_kb": 64,
                "rom_size_kb": 16
            }
        }
    },
    "application": {
        "name": "Application Profile",
        "description": "Medium RV32IMAC for IoT and embedded Linux",
        "config": {
            "isa": "RV32IMAC",
            "num_cores": 4,
            "pipeline": "in_order",
            "cache": {
                "icache_size_kb": 16,
                "icache_ways": 4,
                "dcache_size_kb": 16,
                "dcache_ways": 4,
                "l2_cache_size_kb": 128,
                "l2_cache_ways": 8,
                "l3_cache_size_kb": 0
            },
            "features": {
                "branch_predictor": "tournament",
                "ooo_enable": False,
                "mmu_enable": True,
                "fpu_enable": False,
                "atomic_enable": True,
                "compressed_enable": True,
                "vector_enable": False
            },
            "peripherals": {
                "clint": True,
                "plic": True,
                "uart": True,
                "gpio": True,
                "spi": True,
                "i2c": True,
                "ethernet": True
            },
            "memory": {
                "ram_size_mb": 256,
                "rom_size_kb": 64
            }
        }
    },
    "server": {
        "name": "Server Profile",
        "description": "Large RV32IMAC with OoO for application processors",
        "config": {
            "isa": "RV32IMACFV",
            "num_cores": 8,
            "pipeline": "out_of_order",
            "cache": {
                "icache_size_kb": 64,
                "icache_ways": 8,
                "dcache_size_kb": 64,
                "dcache_ways": 8,
                "l2_cache_size_kb": 512,
                "l2_cache_ways": 16,
                "l3_cache_size_mb": 8,
                "l3_cache_ways": 16
            },
            "features": {
                "branch_predictor": "tage",
                "ooo_enable": True,
                "rob_size": 128,
                "rs_size": 64,
                "mmu_enable": True,
                "fpu_enable": True,
                "atomic_enable": True,
                "compressed_enable": True,
                "vector_enable": True
            },
            "peripherals": {
                "clint": True,
                "plic": True,
                "uart": True,
                "gpio": True,
                "spi": True,
                "i2c": True,
                "ethernet": True,
                "pcie": True,
                "ddr_controller": True
            },
            "memory": {
                "ram_size_gb": 16,
                "rom_size_mb": 1
            }
        }
    }
}

class RISCVConfigurator:
    def __init__(self, workspace_path):
        self.workspace = Path(workspace_path)
        self.rtl_path = self.workspace / "rtl"
        self.scripts_path = self.workspace / "scripts"
        self.config_path = self.workspace / "configs"
        self.config_path.mkdir(exist_ok=True)
        
    def generate_config_package(self, config, output_file):
        """Generate SystemVerilog configuration package"""
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        
        content = f"""//=============================================================================
// Generated by configure_riscv.py on {timestamp}
// Configuration: {config.get('profile_name', 'custom')}
//=============================================================================

`ifndef RISCV_CONFIG_GENERATED_PKG_SV
`define RISCV_CONFIG_GENERATED_PKG_SV

package riscv_config_generated_pkg;

    // Core Configuration
    parameter string  CONFIG_ISA           = "{config['isa']}";
    parameter integer CONFIG_NUM_CORES     = {config['num_cores']};
    parameter string  CONFIG_PIPELINE_TYPE = "{config['pipeline']}";
    
    // Cache Configuration
    parameter integer CONFIG_ICACHE_SIZE_KB = {config['cache']['icache_size_kb']};
    parameter integer CONFIG_ICACHE_WAYS    = {config['cache']['icache_ways']};
    parameter integer CONFIG_DCACHE_SIZE_KB = {config['cache']['dcache_size_kb']};
    parameter integer CONFIG_DCACHE_WAYS    = {config['cache']['dcache_ways']};
"""
        
        if config['cache'].get('l2_cache_size_kb', 0) > 0:
            content += f"""    parameter integer CONFIG_L2_SIZE_KB     = {config['cache']['l2_cache_size_kb']};
    parameter integer CONFIG_L2_WAYS        = {config['cache']['l2_cache_ways']};
"""
        
        if config['cache'].get('l3_cache_size_kb', 0) > 0 or config['cache'].get('l3_cache_size_mb', 0) > 0:
            l3_size_kb = config['cache'].get('l3_cache_size_kb', 0) + config['cache'].get('l3_cache_size_mb', 0) * 1024
            content += f"""    parameter integer CONFIG_L3_SIZE_KB     = {l3_size_kb};
    parameter integer CONFIG_L3_WAYS        = {config['cache']['l3_cache_ways']};
"""
        
        # Features
        content += f"""
    // Feature Enables
    parameter bit     CONFIG_BRANCH_PRED_EN = {int(config['features']['branch_predictor'] != 'none')};
    parameter string  CONFIG_BRANCH_PRED    = "{config['features']['branch_predictor']}";
    parameter bit     CONFIG_OOO_EN         = {int(config['features']['ooo_enable'])};
    parameter bit     CONFIG_MMU_EN         = {int(config['features']['mmu_enable'])};
    parameter bit     CONFIG_FPU_EN         = {int(config['features'].get('fpu_enable', False))};
    parameter bit     CONFIG_ATOMIC_EN      = {int(config['features'].get('atomic_enable', False))};
    parameter bit     CONFIG_COMPRESSED_EN  = {int(config['features'].get('compressed_enable', False))};
    parameter bit     CONFIG_VECTOR_EN      = {int(config['features'].get('vector_enable', False))};
"""
        
        if config['features'].get('ooo_enable'):
            content += f"""
    // Out-of-Order Parameters
    parameter integer CONFIG_ROB_SIZE       = {config['features'].get('rob_size', 64)};
    parameter integer CONFIG_RS_SIZE        = {config['features'].get('rs_size', 32)};
"""
        
        # Peripherals
        content += f"""
    // Peripheral Configuration
    parameter bit     CONFIG_CLINT_EN       = {int(config['peripherals']['clint'])};
    parameter bit     CONFIG_PLIC_EN        = {int(config['peripherals']['plic'])};
    parameter bit     CONFIG_UART_EN        = {int(config['peripherals']['uart'])};
    parameter bit     CONFIG_GPIO_EN        = {int(config['peripherals']['gpio'])};
"""
        
        content += """
endpackage : riscv_config_generated_pkg

`endif // RISCV_CONFIG_GENERATED_PKG_SV
"""
        
        with open(output_file, 'w') as f:
            f.write(content)
            
    def generate_makefile(self, config, output_file):
        """Generate Makefile for the configuration"""
        content = f"""# Generated Makefile for RISC-V {config.get('profile_name', 'custom')} configuration
# Generated on {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}

# Configuration
CONFIG_NAME = {config.get('profile_name', 'custom')}
NUM_CORES = {config['num_cores']}
ISA = {config['isa']}

# Directories
RTL_DIR = ../rtl
TB_DIR = ../tb
BUILD_DIR = build_$(CONFIG_NAME)

# Source files
RTL_SOURCES = \\
    $(RTL_DIR)/packages/base/riscv_base_pkg.sv \\
    $(RTL_DIR)/packages/riscv_system_config_pkg.sv \\
    $(RTL_DIR)/core/riscv_types_pkg.sv \\
    $(RTL_DIR)/core/riscv_exception_pkg.sv \\
    $(RTL_DIR)/core/riscv_core_pkg.sv \\
    $(RTL_DIR)/units/alu.sv \\
    $(RTL_DIR)/units/reg_file.sv \\
    $(RTL_DIR)/units/csr_regfile.sv \\
    $(RTL_DIR)/units/fence_unit.sv \\
    $(RTL_DIR)/core/fetch_stage.sv \\
    $(RTL_DIR)/core/decode_stage.sv \\
    $(RTL_DIR)/core/execute_stage.sv \\
    $(RTL_DIR)/core/mem_stage.sv \\
    $(RTL_DIR)/core/writeback_stage.sv \\
    $(RTL_DIR)/core/riscv_core.sv
"""
        
        if config['features'].get('atomic_enable'):
            content += "    $(RTL_DIR)/units/atomic_unit.sv \\\n"
            
        if config['features'].get('fpu_enable'):
            content += "    $(RTL_DIR)/units/fpu.sv \\\n"
            
        if config['features'].get('compressed_enable'):
            content += "    $(RTL_DIR)/units/compress_decoder.sv \\\n"
            
        if config['peripherals']['clint']:
            content += "    $(RTL_DIR)/peripherals/clint.sv \\\n"
            
        if config['peripherals']['plic']:
            content += "    $(RTL_DIR)/peripherals/plic.sv \\\n"
            
        content += """
# Default target
all: compile

# Create build directory
$(BUILD_DIR):
\tmkdir -p $(BUILD_DIR)

# Compile with Verilator
compile_verilator: $(BUILD_DIR)
\tverilator --sv --cc --exe --build \\
\t\t--top-module riscv_core \\
\t\t-I$(RTL_DIR)/packages \\
\t\t-I$(RTL_DIR)/core \\
\t\t-I$(RTL_DIR) \\
\t\t$(RTL_SOURCES) \\
\t\t-o $(BUILD_DIR)/Vriscv_core

# Compile with Icarus Verilog
compile_iverilog: $(BUILD_DIR)
\tiverilog -g2012 -o $(BUILD_DIR)/riscv_core.vvp \\
\t\t-I $(RTL_DIR)/packages \\
\t\t-I $(RTL_DIR)/core \\
\t\t$(RTL_SOURCES)

# Run simulation
sim: compile_iverilog
\tvvp $(BUILD_DIR)/riscv_core.vvp

# Clean build artifacts
clean:
\trm -rf $(BUILD_DIR)

.PHONY: all compile compile_verilator compile_iverilog sim clean
"""
        
        with open(output_file, 'w') as f:
            f.write(content)
            
    def generate_documentation(self, config, output_file):
        """Generate configuration documentation"""
        content = f"""# RISC-V Configuration: {config.get('profile_name', 'custom')}

Generated on: {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}

## Overview

This configuration implements a {config['isa']} RISC-V processor with the following characteristics:

- **ISA**: {config['isa']}
- **Number of Cores**: {config['num_cores']}
- **Pipeline Type**: {config['pipeline']}

## Cache Hierarchy

| Level | Size | Ways | Line Size |
|-------|------|------|-----------|
| L1 I-Cache | {config['cache']['icache_size_kb']} KB | {config['cache']['icache_ways']} | 64B |
| L1 D-Cache | {config['cache']['dcache_size_kb']} KB | {config['cache']['dcache_ways']} | 64B |
"""
        
        if config['cache'].get('l2_cache_size_kb', 0) > 0:
            content += f"| L2 Cache | {config['cache']['l2_cache_size_kb']} KB | {config['cache']['l2_cache_ways']} | 64B |\n"
            
        if config['cache'].get('l3_cache_size_kb', 0) > 0 or config['cache'].get('l3_cache_size_mb', 0) > 0:
            l3_size = config['cache'].get('l3_cache_size_mb', 0)
            if l3_size == 0:
                l3_size = config['cache'].get('l3_cache_size_kb', 0) / 1024
            content += f"| L3 Cache | {l3_size} MB | {config['cache']['l3_cache_ways']} | 64B |\n"
        
        content += f"""
## Features

- **Branch Predictor**: {config['features']['branch_predictor']}
- **Out-of-Order Execution**: {'Enabled' if config['features']['ooo_enable'] else 'Disabled'}
- **MMU**: {'Enabled' if config['features']['mmu_enable'] else 'Disabled'}
- **FPU**: {'Enabled' if config['features'].get('fpu_enable', False) else 'Disabled'}
- **Atomic Instructions**: {'Enabled' if config['features'].get('atomic_enable', False) else 'Disabled'}
- **Compressed Instructions**: {'Enabled' if config['features'].get('compressed_enable', False) else 'Disabled'}
- **Vector Instructions**: {'Enabled' if config['features'].get('vector_enable', False) else 'Disabled'}

## Peripherals

| Peripheral | Status |
|------------|--------|
| CLINT (Timer) | {'Enabled' if config['peripherals']['clint'] else 'Disabled'} |
| PLIC (Interrupts) | {'Enabled' if config['peripherals']['plic'] else 'Disabled'} |
| UART | {'Enabled' if config['peripherals']['uart'] else 'Disabled'} |
| GPIO | {'Enabled' if config['peripherals']['gpio'] else 'Disabled'} |
"""
        
        if 'spi' in config['peripherals']:
            content += f"| SPI | {'Enabled' if config['peripherals']['spi'] else 'Disabled'} |\n"
        if 'i2c' in config['peripherals']:
            content += f"| I2C | {'Enabled' if config['peripherals']['i2c'] else 'Disabled'} |\n"
        if 'ethernet' in config['peripherals']:
            content += f"| Ethernet | {'Enabled' if config['peripherals'].get('ethernet', False) else 'Disabled'} |\n"
            
        content += """
## Building

To build this configuration:

```bash
cd configs/""" + config.get('profile_name', 'custom') + """
make compile_verilator  # For Verilator
make compile_iverilog   # For Icarus Verilog
```

## Testing

Run the test suite:

```bash
make test
```

## Integration

To integrate this core into your SoC:

1. Include the generated configuration package
2. Instantiate the `riscv_core` module
3. Connect the bus interfaces
4. Configure memory maps for peripherals
"""
        
        with open(output_file, 'w') as f:
            f.write(content)
    
    def configure(self, profile_name, custom_config=None):
        """Configure the RISC-V core with the specified profile"""
        
        # Get configuration
        if profile_name == "custom":
            if not custom_config:
                raise ValueError("Custom configuration file required for 'custom' profile")
            with open(custom_config, 'r') as f:
                config = json.load(f)
        else:
            if profile_name not in PROFILES:
                raise ValueError(f"Unknown profile: {profile_name}")
            config = PROFILES[profile_name]['config'].copy()
            config['profile_name'] = profile_name
            
        # Create configuration directory
        config_dir = self.config_path / profile_name
        config_dir.mkdir(exist_ok=True)
        
        # Generate files
        print(f"Generating configuration for {profile_name} profile...")
        
        # Generate SystemVerilog package
        sv_file = config_dir / "riscv_config_generated_pkg.sv"
        self.generate_config_package(config, sv_file)
        print(f"  Generated: {sv_file}")
        
        # Generate Makefile
        makefile = config_dir / "Makefile"
        self.generate_makefile(config, makefile)
        print(f"  Generated: {makefile}")
        
        # Generate documentation
        doc_file = config_dir / "README.md"
        self.generate_documentation(config, doc_file)
        print(f"  Generated: {doc_file}")
        
        # Save configuration JSON
        config_json = config_dir / "config.json"
        with open(config_json, 'w') as f:
            json.dump(config, f, indent=2)
        print(f"  Generated: {config_json}")
        
        print(f"\nConfiguration complete! Files saved to: {config_dir}")
        print(f"\nTo build: cd {config_dir} && make")
        
        return config_dir

def main():
    parser = argparse.ArgumentParser(description="RISC-V Core Configuration Tool")
    parser.add_argument("--profile", "-p", required=True, 
                       choices=list(PROFILES.keys()) + ["custom"],
                       help="Configuration profile to use")
    parser.add_argument("--custom-config", "-c",
                       help="Path to custom configuration JSON file (required for 'custom' profile)")
    parser.add_argument("--workspace", "-w", default=".",
                       help="Path to workspace directory (default: current directory)")
    parser.add_argument("--list-profiles", "-l", action="store_true",
                       help="List available profiles and exit")
    
    args = parser.parse_args()
    
    if args.list_profiles:
        print("Available RISC-V Configuration Profiles:\n")
        for name, profile in PROFILES.items():
            print(f"{name:12} - {profile['description']}")
        return
    
    # Create configurator
    configurator = RISCVConfigurator(args.workspace)
    
    try:
        # Configure the core
        config_dir = configurator.configure(args.profile, args.custom_config)
        
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()