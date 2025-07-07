# RISC-V Core Verification Plan

## Overview

This document outlines the comprehensive verification strategy for the RISC-V core implementation. The verification plan covers unit-level testing, integration testing, compliance testing, and performance benchmarking to ensure the core meets RISC-V specification requirements and performance targets.

## Verification Strategy

### Verification Goals
- **Functional Correctness:** 100% RISC-V RV32IM compliance
- **Performance Validation:** Meet target IPC and frequency goals
- **Robustness:** Handle all corner cases and error conditions
- **Reliability:** Stable operation under various workloads

### Verification Methodology
- **Unit Testing:** Individual module verification
- **Integration Testing:** Pipeline stage interaction verification
- **System Testing:** Full core functionality verification
- **Compliance Testing:** RISC-V specification compliance
- **Performance Testing:** Benchmark and performance analysis

## Test Categories

### 1. Unit Tests

#### Out-of-Order Engine Tests
**Location:** `tb/tests/unit_tests/ooo_engine_test.sv`

**Test Cases:**
- **Instruction Dispatch:** Verify correct dispatch to RS and ROB.
- **Register Renaming:** Test WAR/WAW hazard elimination and PRF updates.
- **Operand Forwarding:** Verify RAW hazard resolution via CDB.
- **Instruction Issue:** Test correct instruction issue from RS to FUs.
- **In-Order Commit:** Verify in-order retirement from ROB.
- **Precise Exceptions:** Test exception handling and pipeline flush in OoO mode.
- **ROB/RS Full/Empty:** Test boundary conditions for ROB and RS.
- **Parameter Consistency:** Verify that `ooo_pkg.sv` correctly utilizes parameters from `riscv_config_pkg.sv`.
- **Execution Mode Control:** Verify that the OoO engine is correctly enabled/disabled based on the `EXECUTION_MODE` parameter in `core_subsystem.sv`.

**Coverage Goals:**
- **Functional Coverage:** 100% coverage of RS/ROB states, renaming scenarios, and issue logic.
- **Code Coverage:** >95% line coverage for OoO modules.
- **Branch Coverage:** >90% branch coverage for OoO control logic.

#### ALU Unit Tests
**Location:** `tb/tests/unit_tests/alu_test.sv`

**Test Cases:**
- **Arithmetic Operations:** ADD, SUB, SLT, SLTU
- **Logical Operations:** AND, OR, XOR
- **Shift Operations:** SLL, SRL, SRA
- **Overflow Detection:** ADD/SUB overflow scenarios
- **Corner Cases:** Zero operands, maximum values

**Coverage Goals:**
- **Functional Coverage:** 100% operation coverage
- **Code Coverage:** >95% line coverage
- **Branch Coverage:** >90% branch coverage

#### Register File Tests
**Location:** `tb/tests/unit_tests/reg_file_test.sv`

**Test Cases:**
- **Read Operations:** Single and dual-port reads
- **Write Operations:** Register updates
- **Hazard Scenarios:** Read-after-write conditions
- **Reset Behavior:** Register initialization
- **Corner Cases:** x0 register behavior

#### Branch Predictor Tests
**Location:** `tb/tests/unit_tests/branch_predictor_test.sv`

**Test Cases:**
- **Prediction Accuracy:** Various branch patterns
- **BTB Operations:** Hit/miss scenarios
- **BHT Updates:** Counter saturation behavior
- **Global History:** History register updates
- **Performance:** Prediction latency measurement

#### Multiplier/Divider Tests
**Location:** `tb/tests/unit_tests/mult_unit_test.sv`, `tb/tests/unit_tests/div_unit_test.sv`

**Test Cases:**
- **Multiplication:** All RV32M multiply operations
- **Division:** All RV32M divide operations
- **Exception Handling:** Division by zero, overflow
- **Multi-cycle Behavior:** Stall and completion logic
- **Corner Cases:** Maximum/minimum operands

### 2. Integration Tests

#### Pipeline Integration Tests
**Location:** `tb/tests/integration_tests/pipeline_test.sv`

**Test Cases:**
- **Data Hazards:** RAW, WAW hazard scenarios
- **Control Hazards:** Branch misprediction recovery
- **Structural Hazards:** Multi-cycle operation stalls
- **Forwarding Logic:** EX/MEM and MEM/WB forwarding
- **Pipeline Flush:** Exception and branch recovery

#### Memory Interface Tests
**Location:** `tb/tests/integration_tests/memory_test.sv`

**Test Cases:**
- **Load Operations:** Byte, halfword, word loads
- **Store Operations:** Byte, halfword, word stores
- **AXI4-Lite Protocol:** Handshake compliance
- **Memory Alignment:** Proper address alignment
- **Wait States:** Memory access delays

#### Hazard Unit Tests
**Location:** `tb/tests/integration_tests/hazard_test.sv`

**Test Cases:**
- **Data Hazard Detection:** Forwarding path selection
- **Control Hazard Detection:** Pipeline flush generation
- **Stall Logic:** Multi-cycle operation stalls
- **Forwarding Logic:** Correct operand selection
- **Performance Impact:** IPC measurement

#### Feature Enablement Tests
**Location:** `tb/tests/integration_tests/feature_enablement_test.sv`

**Test Cases:**
- **MMU Enablement:** Verify MMU functionality when `CONFIG_ENABLE_MMU` is true, and bypass/disabled behavior when false.
- **QoS Enablement:** Verify QoS functionality when `CONFIG_ENABLE_QOS` is true, and disabled behavior when false.
- **Parameter Propagation:** Verify that `CONFIG_ENABLE_MMU` and `CONFIG_ENABLE_QOS` parameters are correctly propagated from `riscv_config_pkg.sv` through `riscv_core.sv` to `core_subsystem.sv`.

### 3. Compliance Tests

#### RISC-V Compliance Tests
**Location:** `tb/tests/compliance_tests/`

**Test Categories:**
- **RV32I Base Tests:** All base integer instructions
- **RV32M Multiply Tests:** Multiplication instruction compliance
- **RV32M Divide Tests:** Division instruction compliance
- **RV32Zicsr Tests:** CSR operation compliance

**Test Sources:**
- **Official RISC-V Compliance:** https://github.com/riscv/riscv-compliance
- **Custom Compliance Tests:** Project-specific test cases
- **Corner Case Tests:** Edge condition verification

#### Exception Handling Tests
**Location:** `tb/tests/compliance_tests/exception_test.sv`

**Test Cases:**
- **Arithmetic Exceptions:** Division by zero, overflow
- **Memory Exceptions:** Misaligned access
- **Control Exceptions:** Illegal instruction
- **System Exceptions:** ECALL, EBREAK
- **Exception Priority:** Multiple exception handling

### 4. Performance Tests

#### Benchmark Tests
**Location:** `tb/tests/performance_tests/`

**Benchmark Programs:**
- **Dhrystone:** Integer performance benchmark
- **CoreMark:** Embedded benchmark suite
- **Branch-heavy Workloads:** Branch prediction testing
- **Memory-intensive Workloads:** Memory access patterns
- **Custom Benchmarks:** Project-specific performance tests

**Performance Metrics:**
- **IPC (Instructions Per Cycle):** Target >0.8
- **Branch Prediction Accuracy:** Target >85%
- **Pipeline Efficiency:** Target >70%
- **Memory Bandwidth:** Load/store performance
- **Power Efficiency:** Energy per instruction

#### Stress Tests
**Location:** `tb/tests/performance_tests/stress_test.sv`

**Test Scenarios:**
- **High-frequency Branching:** Branch prediction stress
- **Memory Access Patterns:** Cache-friendly and cache-unfriendly
- **Multi-cycle Operation Mix:** ALU, multiply, divide combinations
- **Exception Frequency:** High exception rate scenarios
- **Long-running Programs:** Stability over extended periods

#### QoS Tests
**Location:** `tb/tests/performance_tests/qos_test.sv` (or integrated into `qos_stress_tb.sv`)

**Test Cases:**
- **Priority Enforcement:** Verify that critical transactions are prioritized over lower-priority ones.
- **Bandwidth Allocation:** Test if bandwidth guarantees are met under contention.
- **Latency Guarantees:** Measure and verify that critical transactions meet their maximum latency cycles.
- **Fairness:** Ensure that lower-priority transactions are not starved under heavy load.
- **QoS Violation Detection:** Verify that the QoS monitor correctly identifies and reports violations.
- **Dynamic QoS Changes:** Test the system's response to real-time changes in QoS parameters.

**Coverage Goals:**
- **Functional Coverage:** 100% coverage of QoS levels, transaction types, and priority scenarios.
- **Code Coverage:** >95% line and branch coverage for QoS-related logic.

## Test Infrastructure

### Testbench Architecture
**Location:** `tb/testbench/`

**Components:**
- **Test Harness:** `test_harness.sv` - Main test coordination
- **Clock Generator:** `clock_gen.sv` - Clock generation and management
- **Memory Model:** `memory_model.sv` - Behavioral memory model
- **Scoreboard:** `scoreboard.sv` - Result checking and verification
- **Coverage Monitor:** `coverage_monitor.sv` - Coverage collection

### Memory Models
**Location:** `tb/models/`

**Models:**
- **Instruction Memory:** `instruction_memory.sv` - Instruction storage
- **Data Memory:** `data_memory.sv` - Data storage with AXI4-Lite interface
- **Cache Models:** `icache_model.sv`, `dcache_model.sv` - Cache behavior models
- **Peripheral Models:** `uart_model.sv`, `timer_model.sv` - Peripheral behavior

### Verification IP
**Location:** `tb/vip/`

**Components:**
- **AXI4-Lite Monitor:** `axi4_lite_monitor.sv` - Protocol compliance checking
- **Performance Monitor:** `performance_monitor.sv` - Performance metrics collection
- **Assertion Checker:** `assertion_checker.sv` - Design assertion verification
- **Coverage Collector:** `coverage_collector.sv` - Functional coverage collection

## Coverage Strategy

### Functional Coverage
**Coverage Points:**
- **Instruction Coverage:** All RV32IM instructions executed
- **Operand Coverage:** Various operand value combinations
- **Hazard Coverage:** All hazard types and resolutions
- **Exception Coverage:** All exception types and handling
- **Branch Coverage:** All branch types and outcomes

### Code Coverage
**Coverage Types:**
- **Line Coverage:** All code lines executed
- **Branch Coverage:** All conditional branches taken
- **Expression Coverage:** Complex expression evaluation
- **Toggle Coverage:** Signal value changes
- **FSM Coverage:** State machine transitions

### Performance Coverage
**Coverage Metrics:**
- **IPC Distribution:** Various IPC values achieved
- **Branch Prediction Accuracy:** Prediction success rates
- **Memory Access Patterns:** Different access types
- **Pipeline Utilization:** Stage utilization rates
- **Resource Usage:** Functional unit utilization

## Test Automation

### Test Runner Scripts
**Location:** `tb/scripts/`

**Scripts:**
- **run_tests.py:** Main test execution script
- **coverage.py:** Coverage analysis and reporting
- **regression.py:** Regression test execution
- **performance.py:** Performance benchmark execution
- **compliance.py:** RISC-V compliance test execution

### Continuous Integration
**Location:** `ci/.github/workflows/`

**Workflows:**
- **lint.yml:** Code linting and style checking
- **test.yml:** Automated test execution
- **build.yml:** Synthesis and build verification
- **coverage.yml:** Coverage reporting and analysis

### Test Configuration
**Location:** `tb/config/`

**Configuration Files:**
- **test_config.yaml:** Test execution configuration
- **coverage_config.yaml:** Coverage collection configuration
- **performance_config.yaml:** Performance test configuration
- **compliance_config.yaml:** Compliance test configuration

## Verification Tools

### Simulation Tools
- **ModelSim/QuestaSim:** Primary simulation environment
- **VCS:** Synopsys VCS for high-performance simulation
- **Verilator:** Open-source simulation for CI/CD
- **Xcelium:** Cadence Xcelium for advanced verification

### Coverage Tools
- **Coverage Metrics:** Built-in SystemVerilog coverage
- **Coverage Analysis:** Coverage reporting and analysis
- **Coverage Visualization:** Coverage visualization tools
- **Coverage Optimization:** Coverage-driven test generation

### Formal Verification
- **Model Checking:** Formal property verification
- **Equivalence Checking:** RTL-to-RTL equivalence
- **Assertion Verification:** Formal assertion checking
- **Coverage Verification:** Formal coverage analysis

## Verification Schedule

### Phase 1: Unit Testing (Week 1-2)
- [ ] ALU unit tests
- [ ] Register file tests
- [ ] Branch predictor tests
- [ ] Multiplier/divider tests
- [ ] Basic coverage collection

### Phase 2: Integration Testing (Week 3-4)
- [ ] Pipeline integration tests
- [ ] Memory interface tests
- [ ] Hazard unit tests
- [ ] Exception handling tests
- [ ] Integration coverage

### Phase 3: Compliance Testing (Week 5-6)
- [ ] RISC-V compliance tests
- [ ] Exception handling compliance
- [ ] CSR operation compliance
- [ ] Compliance coverage
- [ ] Compliance reporting

### Phase 4: Performance Testing (Week 7-8)
- [ ] Benchmark execution
- [ ] Performance analysis
- [ ] Stress testing
- [ ] Performance optimization
- [ ] Final verification report

## Success Criteria

### Functional Correctness
- **100% RISC-V Compliance:** All RV32IM instructions pass compliance tests
- **Exception Handling:** All exceptions handled correctly
- **Hazard Resolution:** All hazards resolved without functional errors
- **Memory Operations:** All memory operations execute correctly

### Performance Targets
- **IPC > 0.8:** Instructions per cycle target met
- **Branch Prediction > 85%:** Branch prediction accuracy target
- **Pipeline Efficiency > 70%:** Pipeline utilization target
- **Frequency Target:** 100+ MHz (FPGA), 500+ MHz (ASIC)

### Quality Metrics
- **Code Coverage > 95%:** High code coverage achieved
- **Functional Coverage > 90%:** Comprehensive functional coverage
- **Zero Critical Bugs:** No critical functional bugs
- **Regression Stability:** All regression tests pass consistently

## Risk Mitigation

### Verification Risks
- **Incomplete Coverage:** Mitigated by comprehensive coverage strategy
- **Performance Shortfalls:** Mitigated by early performance testing
- **Compliance Issues:** Mitigated by official compliance test suite
- **Integration Problems:** Mitigated by systematic integration testing

### Mitigation Strategies
- **Early Verification:** Start verification early in development
- **Automated Testing:** Comprehensive test automation
- **Continuous Integration:** Regular verification execution
- **Coverage-Driven Testing:** Coverage-guided test development

---

**Verification Plan Version:** 1.0  
**Last Updated:** June 2025  
**Core Version:** RV32IM 5-stage Pipeline 