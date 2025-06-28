# Troubleshooting Guide

## Common Issues and Solutions

This guide provides solutions to common problems encountered when working with the RISC-V core implementation. If you don't find your issue here, please check the GitHub issues or create a new one.

## Compilation Issues

### SystemVerilog Compilation Errors

#### Problem: Package Import Errors
```
Error: Cannot find package 'riscv_core_pkg'
```

**Solution:**
1. Ensure `riscv_core_pkg.sv` is compiled first:
   ```bash
   vlog rtl/core/riscv_core_pkg.sv
   vlog rtl/units/*.sv
   vlog rtl/control/*.sv
   vlog rtl/prediction/*.sv
   vlog rtl/core/*.sv
   ```

2. Check file paths are correct in your compilation script
3. Verify the package file exists in `rtl/core/riscv_core_pkg.sv`

#### Problem: Module Not Found
```
Error: Module 'branch_predictor' not found
```

**Solution:**
1. Ensure all RTL files are compiled:
   ```bash
   # Compile all files in dependency order
   vlog rtl/core/riscv_core_pkg.sv
   vlog rtl/units/*.sv
   vlog rtl/control/*.sv
   vlog rtl/prediction/*.sv
   vlog rtl/core/*.sv
   ```

2. Check that `rtl/prediction/branch_predictor.sv` exists
3. Verify module name matches file name

#### Problem: Syntax Errors
```
Error: Unexpected token 'typedef'
```

**Solution:**
1. Check SystemVerilog syntax:
   - Ensure semicolons are present
   - Verify bracket matching
   - Check for missing `endmodule` statements

2. Use a SystemVerilog linter:
   ```bash
   # Install Verilator for linting
   verilator --lint-only rtl/core/riscv_core.sv
   ```

### Tool-Specific Issues

#### ModelSim/QuestaSim Issues
**Problem:** Simulation doesn't start
```
Error: Failed to load design
```

**Solution:**
1. Check work library exists:
   ```tcl
   vlib work
   ```

2. Verify compilation order:
   ```tcl
   vlog rtl/core/riscv_core_pkg.sv
   vlog rtl/units/*.sv
   vlog rtl/control/*.sv
   vlog rtl/prediction/*.sv
   vlog rtl/core/*.sv
   ```

3. Check for missing dependencies

#### Verilator Issues
**Problem:** Verilator compilation fails
```
Error: Unsupported language construct
```

**Solution:**
1. Use Verilator 4.0+ for SystemVerilog support
2. Add `--language 1800-2017` flag:
   ```bash
   verilator --language 1800-2017 --cc rtl/core/riscv_core.sv
   ```

3. Check for unsupported SystemVerilog constructs

## Simulation Issues

### Simulation Hangs or Stalls

#### Problem: Simulation Doesn't Progress
**Symptoms:** Simulation runs but no instructions execute

**Diagnosis:**
1. Check reset signal:
   ```systemverilog
   // Ensure reset is properly asserted then de-asserted
   initial begin
       rst_ni = 0;
       #100;
       rst_ni = 1;
   end
   ```

2. Check memory interface:
   ```systemverilog
   // Verify AXI4-Lite handshaking
   always @(posedge clk_i) begin
       if (i_arvalid_o && !i_arready_i) begin
           // Memory not ready - this is normal
       end
   end
   ```

**Solution:**
1. Ensure proper reset sequence
2. Check memory model is responding
3. Verify clock generation is working

#### Problem: Infinite Loop
**Symptoms:** Simulation runs forever without completing

**Diagnosis:**
1. Check for infinite loops in test programs
2. Verify branch prediction is working
3. Check for memory access issues

**Solution:**
1. Add timeout to simulation:
   ```tcl
   # In ModelSim
   run 10000ns
   ```

2. Add debug prints:
   ```systemverilog
   always @(posedge clk_i) begin
       if (rst_ni) begin
           $display("PC: %h, Instruction: %h", pc_f_o, if_id_reg_o.instr);
       end
   end
   ```

### Memory Interface Issues

#### Problem: AXI4-Lite Protocol Violations
**Symptoms:** Memory transactions fail or hang

**Diagnosis:**
1. Check handshake signals:
   ```systemverilog
   // Valid signals must be held until ready
   always @(posedge clk_i) begin
       if (i_arvalid_o && i_arready_i) begin
           // Transaction completed
       end
   end
   ```

2. Verify address alignment:
   ```systemverilog
   // RISC-V requires aligned memory access
   if (address[1:0] != 2'b00) begin
       // Misaligned access
   end
   ```

**Solution:**
1. Ensure proper AXI4-Lite handshaking
2. Check memory model implementation
3. Verify address alignment requirements

#### Problem: Memory Access Errors
**Symptoms:** Load/store operations fail

**Diagnosis:**
1. Check memory model initialization
2. Verify address ranges
3. Check byte enables for stores

**Solution:**
1. Initialize memory model properly
2. Check address decoding
3. Verify byte enable logic

## Functional Issues

### Branch Prediction Problems

#### Problem: Low Branch Prediction Accuracy
**Symptoms:** Many branch mispredictions, low IPC

**Diagnosis:**
1. Check BTB and BHT initialization:
   ```systemverilog
   // BTB should be initialized to invalid
   initial begin
       for (int i = 0; i < BTB_ENTRIES; i++) begin
           btb_mem[i].valid = 1'b0;
       end
   end
   ```

2. Verify update logic:
   ```systemverilog
   // Check branch prediction updates
   always @(posedge clk_i) begin
       if (bp_update_i.update_valid) begin
           // Update should occur
       end
   end
   ```

**Solution:**
1. Ensure proper BTB/BHT initialization
2. Check branch prediction update timing
3. Verify global history register updates

#### Problem: Branch Target Buffer Full
**Symptoms:** BTB misses even for frequently taken branches

**Diagnosis:**
1. Check BTB size configuration
2. Monitor BTB replacement policy
3. Check for BTB conflicts

**Solution:**
1. Increase BTB size if needed
2. Implement better replacement policy
3. Check for address conflicts

### Hazard Detection Issues

#### Problem: Data Hazards Not Detected
**Symptoms:** Incorrect results due to data dependencies

**Diagnosis:**
1. Check forwarding logic:
   ```systemverilog
   // Verify forwarding path selection
   always @(*) begin
       case (forward_a_sel_i)
           FWD_SEL_REG: fwd_operand_a = id_ex_reg_i.rs1_data;
           FWD_SEL_MEM: fwd_operand_a = ex_mem_reg_m_i.alu_result;
           FWD_SEL_WB:  fwd_operand_a = wb_data_w_i;
       endcase
   end
   ```

2. Verify hazard detection:
   ```systemverilog
   // Check hazard detection logic
   assign data_hazard = (rs1_addr_d_i == rd_addr_ex_i) && reg_write_en_ex_i;
   ```

**Solution:**
1. Check hazard detection logic
2. Verify forwarding path selection
3. Ensure register addresses are compared correctly

#### Problem: Pipeline Stalls Not Working
**Symptoms:** Multi-cycle operations cause incorrect results

**Diagnosis:**
1. Check stall signal generation:
   ```systemverilog
   // Multi-cycle operations should generate stalls
   assign exec_stall_req_o = (mult_en && !mult_done) || (div_en && !div_done);
   ```

2. Verify stall propagation:
   ```systemverilog
   // Stalls should propagate through pipeline
   assign stall_f = exec_stall_req_i || memory_stall_i;
   ```

**Solution:**
1. Check stall signal generation logic
2. Verify stall propagation through pipeline
3. Ensure multi-cycle operations complete properly

## Performance Issues

### Low IPC (Instructions Per Cycle)

#### Problem: IPC Below Target (< 0.8)
**Diagnosis:**
1. Check for frequent stalls:
   ```systemverilog
   // Monitor stall frequency
   always @(posedge clk_i) begin
       if (stall_f) stall_count <= stall_count + 1;
   end
   ```

2. Check branch prediction accuracy:
   ```systemverilog
   // Monitor branch prediction
   always @(posedge clk_i) begin
       if (branch_taken != predict_taken) begin
           misprediction_count <= misprediction_count + 1;
       end
   end
   ```

**Solution:**
1. Optimize branch prediction
2. Reduce memory access latency
3. Minimize multi-cycle operations

#### Problem: Memory Bottleneck
**Symptoms:** High memory wait states

**Diagnosis:**
1. Check memory access patterns
2. Monitor AXI4-Lite handshaking
3. Check memory model performance

**Solution:**
1. Implement instruction cache (Phase 1)
2. Optimize memory access patterns
3. Use burst transfers if possible

## Synthesis Issues

### FPGA Synthesis Problems

#### Problem: Synthesis Fails
**Symptoms:** Synthesis tool reports errors

**Diagnosis:**
1. Check for unsupported SystemVerilog constructs
2. Verify parameter values are within FPGA limits
3. Check for timing violations

**Solution:**
1. Use synthesis-compatible SystemVerilog subset
2. Adjust parameter values for target FPGA
3. Add timing constraints

#### Problem: Timing Violations
**Symptoms:** Critical path violations

**Diagnosis:**
1. Check clock frequency constraints
2. Analyze critical paths
3. Check for combinational loops

**Solution:**
1. Add proper timing constraints
2. Optimize critical paths
3. Consider pipelining optimizations

### ASIC Synthesis Issues

#### Problem: Area Too Large
**Symptoms:** Design exceeds area budget

**Diagnosis:**
1. Check for unnecessary logic
2. Analyze resource utilization
3. Check for redundant operations

**Solution:**
1. Optimize logic implementation
2. Use smaller data types where possible
3. Consider resource sharing

## Debugging Techniques

### Waveform Analysis

#### Using ModelSim/QuestaSim
```tcl
# Add all signals to waveform
add wave -position insertpoint sim:/riscv_core/*

# Add specific signals
add wave -position insertpoint sim:/riscv_core/u_fetch_stage/*
add wave -position insertpoint sim:/riscv_core/u_execute_stage/*

# Run simulation with waveform
vsim -gui riscv_core
run -all
```

#### Using GTKWave
```bash
# Generate VCD file
verilator --trace --cc rtl/core/riscv_core.sv

# View with GTKWave
gtkwave dump.vcd
```

### Signal Monitoring

#### Add Debug Prints
```systemverilog
// Add to modules for debugging
always @(posedge clk_i) begin
    if (rst_ni && debug_enable) begin
        $display("Time: %0t, PC: %h, Instruction: %h", $time, pc_f_o, if_id_reg_o.instr);
    end
end
```

#### Performance Counters
```systemverilog
// Add performance monitoring
always @(posedge clk_i) begin
    if (rst_ni) begin
        cycle_count <= cycle_count + 1;
        if (branch_taken) branch_count <= branch_count + 1;
        if (stall_f) stall_count <= stall_count + 1;
    end
end
```

### Assertion Checking

#### Add Assertions
```systemverilog
// Add assertions for debugging
always @(posedge clk_i) begin
    if (rst_ni) begin
        // Check for valid PC
        assert (pc_f_o[1:0] == 2'b00) else 
            $error("PC not aligned: %h", pc_f_o);
        
        // Check for valid instruction
        assert (if_id_reg_o.valid || if_id_reg_o.instr == NOP_INSTRUCTION) else
            $error("Invalid instruction: %h", if_id_reg_o.instr);
    end
end
```

## Getting Help

### Before Asking for Help

1. **Check this guide** for your specific issue
2. **Search GitHub issues** for similar problems
3. **Check documentation** in `docs/` directory
4. **Verify your setup** matches requirements

### When Creating an Issue

Include the following information:
1. **Problem description** - What you're trying to do
2. **Error messages** - Exact error text
3. **Environment** - Tool versions, OS, etc.
4. **Steps to reproduce** - Detailed steps
5. **Expected vs actual behavior** - What you expected vs what happened

### Example Issue Template
```
**Problem:** [Brief description]

**Environment:**
- Tool: [ModelSim/VCS/Verilator/etc.]
- Version: [Tool version]
- OS: [Operating system]
- RISC-V Core Version: [Git commit hash]

**Steps to Reproduce:**
1. [Step 1]
2. [Step 2]
3. [Step 3]

**Expected Behavior:** [What should happen]

**Actual Behavior:** [What actually happens]

**Error Messages:**
```
[Paste error messages here]
```

**Additional Information:**
[Any other relevant details]
```

## Resources

### Documentation
- **[Getting Started Guide](getting_started.md):** Quick start instructions
- **[Pipeline Architecture](../architecture/pipeline.md):** Detailed architecture
- **[Verification Plan](../implementation/verification_plan.md):** Testing strategy

### External Resources
- **[RISC-V Specification](https://riscv.org/specifications/):** Official RISC-V documentation
- **[SystemVerilog LRM](https://ieeexplore.ieee.org/document/8299595):** Language reference
- **[AXI4-Lite Specification](https://developer.arm.com/documentation/ihi0022/e/):** Memory interface specification

### Community Support
- **GitHub Issues:** Report bugs and request features
- **GitHub Discussions:** Ask questions and share ideas
- **RISC-V Community:** Official RISC-V community forums

---

**Troubleshooting Guide Version:** 1.0  
**Last Updated:** June 2025  
**Core Version:** RV32IM 5-stage Pipeline 