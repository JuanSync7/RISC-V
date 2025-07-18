# RISC-V Core Directory Structure

## ✅ **REORGANIZATION COMPLETED**

This document outlines the completed directory structure reorganization for the RISC-V core project, designed to accommodate current implementation and future enhancements including Phase 1 improvements and beyond.

## 🎯 **Migration Summary**

### ✅ **Completed Tasks**
- [x] Created comprehensive directory structure
- [x] Moved all RTL files to appropriate locations
- [x] Organized documentation into logical categories
- [x] Updated README.md with new structure
- [x] Created comprehensive .gitignore file
- [x] Verified import paths work correctly

### 📁 **Current Directory Structure**

```
RISC-V/
├── 📚 Documentation
│   ├── docs/
│   │   ├── README.md                    # Documentation index
│   │   ├── architecture/                # Architecture documentation
│   │   ├── implementation/              # Implementation details
│   │   └── user_guide/                  # User guides and tutorials
│   ├── CURRENT_IMPLEMENTATION.md        # Current implementation details
│   ├── PHASE1_IMPROVEMENTS.md           # Phase 1 improvement roadmap
│   └── README.md                        # Main project README
├── 🔧 RTL Design Files (rtl/)
│   ├── config/                          # Configuration packages
│   │   ├── core/                        # Core-specific configuration
│   │   ├── memory/                      # Memory configuration
│   │   └── protocol/                    # Protocol configuration
│   ├── core/                            # Core processor implementation
│   │   ├── riscv_core.sv                # Top-level core integration
│   │   ├── pipeline/                    # Pipeline stages
│   │   │   ├── fetch_stage.sv           # Instruction fetch stage
│   │   │   ├── decode_stage.sv          # Instruction decode stage
│   │   │   ├── execute_stage.sv         # Execute stage with ALU/Mult/Div
│   │   │   ├── mem_stage.sv             # Memory access stage
│   │   │   └── writeback_stage.sv       # Writeback stage
│   │   ├── control/                     # Control and hazard logic
│   │   │   └── hazard_unit.sv           # Hazard detection and forwarding
│   │   ├── execution/                   # Out-of-order execution
│   │   │   ├── reorder_buffer.sv        # Reorder buffer
│   │   │   ├── reservation_station.sv   # Reservation stations
│   │   │   └── register_renaming.sv     # Register renaming
│   │   ├── prediction/                  # Branch prediction
│   │   │   ├── branch_predictor.sv      # Tournament branch predictor
│   │   │   └── return_stack_buffer.sv   # Return stack buffer
│   │   └── integration/                 # System integration
│   │       ├── core_subsystem.sv        # Core subsystem wrapper
│   │       └── multi_core_system.sv     # Multi-core system
│   ├── memory/                          # Memory subsystem
│   │   ├── cache/                       # Cache implementations
│   │   │   ├── icache.sv                # L1 instruction cache
│   │   │   ├── l2_cache.sv              # L2 shared cache
│   │   │   └── l3_cache.sv              # L3 cache
│   │   ├── coherency/                   # Cache coherency
│   │   │   └── cache_coherency_controller.sv # MESI protocol
│   │   └── wrappers/                    # Memory interface wrappers
│   │       └── memory_wrapper.sv        # Protocol abstraction
│   ├── protocol/                        # Protocol implementations
│   │   ├── axi/                         # AXI4 protocol
│   │   │   └── axi4_adapter.sv          # AXI4 adapter
│   │   ├── chi/                         # CHI protocol
│   │   │   └── chi_adapter.sv           # CHI adapter
│   │   └── tilelink/                    # TileLink protocol
│   │       └── tilelink_adapter.sv      # TileLink adapter
│   ├── shared/                          # Shared components
│   │   ├── interfaces/                  # Interface definitions
│   │   │   ├── axi4_if.sv               # AXI4 interface
│   │   │   ├── chi_if.sv                # CHI interface
│   │   │   └── memory_req_rsp_if.sv     # Generic memory interface
│   │   └── packages/                    # Type definitions
│   │       ├── riscv_core_pkg.sv        # Core types
│   │       ├── riscv_core_types_pkg.sv  # Core data types
│   │       └── riscv_memory_types_pkg.sv # Memory types
│   ├── units/                           # Functional units
│   │   ├── alu.sv                       # Arithmetic Logic Unit
│   │   ├── mult_unit.sv                 # Multi-cycle multiplier
│   │   ├── div_unit.sv                  # Multi-cycle divider
│   │   ├── reg_file.sv                  # 32x32 register file
│   │   └── csr_regfile.sv               # Control and status registers
│   └── peripherals/                     # Peripheral components
│       └── (Future: uart.sv, timer.sv)
├── 🧪 Testbench and Verification (tb/)
│   ├── testbench/                       # Testbench files
│   ├── tests/                           # Test cases
│   ├── models/                          # Behavioral models
│   └── scripts/                         # Test automation
├── 🔬 Simulation (sim/)
│   ├── scripts/                         # Simulation scripts
│   ├── constraints/                     # Timing constraints
│   └── logs/                            # Simulation logs
├── 🔌 FPGA Implementation (fpga/)
│   ├── projects/                        # FPGA project files
│   ├── constraints/                     # FPGA constraints
│   └── bitstreams/                      # Generated bitstreams
├── 🏭 ASIC Implementation (asic/)
│   ├── synthesis/                       # Synthesis files
│   ├── place_route/                     # Place and route files
│   └── verification/                    # ASIC verification
├── 🛠️ Development Tools (tools/)
│   ├── scripts/                         # Utility scripts
│   ├── config/                          # Tool configurations
│   └── templates/                       # Code templates
├── 💻 Software (software/)
│   ├── examples/                        # Example programs
│   ├── benchmarks/                      # Benchmark programs
│   └── tools/                           # Software tools
└── 🔄 Continuous Integration (ci/)
    ├── .github/                         # GitHub Actions
    └── docker/                          # Docker configurations
```

## 🎯 **Benefits Achieved**

1. **✅ Scalability:** Accommodates growth from simple core to complex SoC
2. **✅ Modularity:** Clear separation of concerns and components
3. **✅ Maintainability:** Easy to locate and modify specific components
4. **✅ Reusability:** Components can be easily reused in different projects
5. **✅ Verification:** Comprehensive test organization structure
6. **✅ Documentation:** Clear documentation structure
7. **✅ Tool Integration:** Ready for professional development tools

## 🚀 **Next Steps**

### Phase 1 Improvements (In Progress)
- [ ] **Instruction Cache Implementation** - 4KB 2-way set associative cache
- [ ] **Enhanced Exception Handling** - Complete M-mode exception support

### Future Enhancements
- [ ] **Testbench Development** - Comprehensive verification framework
- [ ] **FPGA Implementation** - Target-specific projects and constraints
- [ ] **Performance Optimization** - Advanced features and optimizations

## 📋 **Compilation Instructions**

With the reorganized directory structure, compile files in this order:

```bash
# 1. Configuration packages (must be first)
vlog rtl/config/core/*.sv

# 2. Shared packages and interfaces
vlog rtl/shared/packages/*.sv
vlog rtl/shared/interfaces/*.sv

# 3. Functional units
vlog rtl/units/*.sv

# 4. Protocol adapters
vlog rtl/protocol/axi/*.sv
vlog rtl/protocol/chi/*.sv
vlog rtl/protocol/tilelink/*.sv

# 5. Memory subsystem
vlog rtl/memory/cache/*.sv
vlog rtl/memory/coherency/*.sv
vlog rtl/memory/wrappers/*.sv

# 6. Core control and prediction
vlog rtl/core/control/*.sv
vlog rtl/core/prediction/*.sv
vlog rtl/core/execution/*.sv

# 7. Core pipeline stages
vlog rtl/core/pipeline/*.sv

# 8. Core integration and top level
vlog rtl/core/integration/*.sv
vlog rtl/core/*.sv

# 9. Run simulation
vsim -c riscv_core -do "run -all; quit"
```

---

**Status:** ✅ **REORGANIZATION COMPLETE**  
**Date:** June 2025  
**Version:** 1.0
