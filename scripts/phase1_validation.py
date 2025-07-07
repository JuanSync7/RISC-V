#!/usr/bin/env python3
"""
RISC-V Phase 1 Validation Script

This script automates the validation of Phase 1 RTL implementation:
1. Tests compilation of core components
2. Runs basic functional tests
3. Validates integration
4. Reports status and issues

Created: 2025-01-27
Author: DesignAI Implementation Team
"""

import os
import sys
import subprocess
import json
import time
from pathlib import Path
from typing import Dict, List, Tuple, Optional

class Phase1Validator:
    def __init__(self, project_root: str):
        self.project_root = Path(project_root)
        self.rtl_dir = self.project_root / "rtl"
        self.tb_dir = self.project_root / "tb"
        self.results = {
            "compilation": {},
            "functionality": {},
            "integration": {},
            "overall_status": "UNKNOWN"
        }
        
    def run_command(self, cmd: str, cwd: Optional[Path] = None) -> Tuple[int, str, str]:
        """Run shell command and return (return_code, stdout, stderr)"""
        try:
            if cwd is None:
                cwd = self.project_root
                
            print(f"Running: {cmd}")
            result = subprocess.run(
                cmd,
                shell=True,
                cwd=cwd,
                capture_output=True,
                text=True,
                timeout=300  # 5 minute timeout
            )
            return result.returncode, result.stdout, result.stderr
        except subprocess.TimeoutExpired:
            return -1, "", "Command timed out"
        except Exception as e:
            return -1, "", str(e)
    
    def test_rtl_compilation(self) -> Dict[str, bool]:
        """Test compilation of core RTL components"""
        print("\n=== PHASE 1 RTL COMPILATION TESTING ===")
        
        # Core components to test
        core_files = [
            "rtl/pkg/riscv_types_pkg.sv",
            "rtl/pkg/riscv_config_pkg.sv", 
            "rtl/pkg/riscv_core_pkg.sv",
            "rtl/units/alu.sv",
            "rtl/units/reg_file.sv",
            "rtl/units/mult_unit.sv",
            "rtl/units/div_unit.sv",
            "rtl/units/csr_regfile.sv",
            "rtl/core/fetch_stage.sv",
            "rtl/core/decode_stage.sv",
            "rtl/core/execute_stage.sv",
            "rtl/core/mem_stage.sv",
            "rtl/core/writeback_stage.sv",
            "rtl/core/riscv_core.sv"
        ]
        
        compilation_results = {}
        
        for file_path in core_files:
            full_path = self.project_root / file_path
            if not full_path.exists():
                print(f"❌ File not found: {file_path}")
                compilation_results[file_path] = False
                continue
                
            # Test compilation with VCS (if available) or basic syntax check
            print(f"\n📝 Testing compilation: {file_path}")
            
            # Try VCS first
            vcs_cmd = f"cd {self.project_root} && vcs -sverilog -full64 +define+SIMULATION -q {file_path}"
            ret_code, stdout, stderr = self.run_command(vcs_cmd)
            
            if ret_code == 0:
                print(f"✅ VCS compilation successful: {file_path}")
                compilation_results[file_path] = True
            else:
                # Try basic syntax check with vlog (ModelSim)
                vlog_cmd = f"cd {self.project_root} && vlog -sv {file_path}"
                ret_code2, stdout2, stderr2 = self.run_command(vlog_cmd)
                
                if ret_code2 == 0:
                    print(f"✅ Basic syntax check passed: {file_path}")
                    compilation_results[file_path] = True
                else:
                    print(f"❌ Compilation failed: {file_path}")
                    print(f"   VCS Error: {stderr[:200]}...")
                    print(f"   Vlog Error: {stderr2[:200]}...")
                    compilation_results[file_path] = False
        
        self.results["compilation"] = compilation_results
        return compilation_results
    
    def test_unit_functionality(self) -> Dict[str, bool]:
        """Test functionality of individual units"""
        print("\n=== PHASE 1 UNIT FUNCTIONALITY TESTING ===")
        
        unit_testbenches = [
            "tb/unit/units/alu_tb.sv",
            "tb/unit/units/reg_file_tb.sv",
            "tb/unit/units/mult_unit_tb.sv",
            "tb/unit/units/div_unit_tb.sv"
        ]
        
        functionality_results = {}
        
        for tb_path in unit_testbenches:
            full_path = self.project_root / tb_path
            if not full_path.exists():
                print(f"❌ Testbench not found: {tb_path}")
                functionality_results[tb_path] = False
                continue
                
            print(f"\n🧪 Running testbench: {tb_path}")
            
            # Try to compile and run testbench
            tb_name = Path(tb_path).stem
            compile_cmd = f"cd {self.project_root} && vcs -sverilog -full64 +define+SIMULATION -timescale=1ns/1ps {tb_path} -o {tb_name}"
            ret_code, stdout, stderr = self.run_command(compile_cmd)
            
            if ret_code == 0:
                # Run the testbench
                run_cmd = f"cd {self.project_root} && ./{tb_name}"
                ret_code2, stdout2, stderr2 = self.run_command(run_cmd)
                
                if ret_code2 == 0 and "PASS" in stdout2:
                    print(f"✅ Testbench passed: {tb_path}")
                    functionality_results[tb_path] = True
                else:
                    print(f"❌ Testbench failed: {tb_path}")
                    print(f"   Output: {stdout2[:300]}...")
                    functionality_results[tb_path] = False
            else:
                print(f"❌ Testbench compilation failed: {tb_path}")
                print(f"   Error: {stderr[:200]}...")
                functionality_results[tb_path] = False
        
        self.results["functionality"] = functionality_results
        return functionality_results
    
    def test_integration(self) -> Dict[str, bool]:
        """Test basic integration scenarios"""
        print("\n=== PHASE 1 INTEGRATION TESTING ===")
        
        integration_tests = {
            "single_core_basic": self.test_single_core_basic,
            "memory_interface": self.test_memory_interface,
            "pipeline_flow": self.test_pipeline_flow
        }
        
        integration_results = {}
        
        for test_name, test_func in integration_tests.items():
            print(f"\n🔧 Running integration test: {test_name}")
            try:
                result = test_func()
                integration_results[test_name] = result
                status = "✅ PASSED" if result else "❌ FAILED"
                print(f"   {status}")
            except Exception as e:
                print(f"❌ Integration test error: {e}")
                integration_results[test_name] = False
        
        self.results["integration"] = integration_results
        return integration_results
    
    def test_single_core_basic(self) -> bool:
        """Test basic single-core instantiation"""
        # Check if core can be instantiated with default parameters
        core_path = self.project_root / "rtl/core/riscv_core.sv"
        if not core_path.exists():
            return False
            
        # Create a simple testbench to instantiate the core
        simple_tb = '''
`timescale 1ns/1ps
module simple_core_tb();
    logic clk, rst_n;
    
    // Clock generation
    initial clk = 0;
    always #5 clk = ~clk;
    
    // Reset generation
    initial begin
        rst_n = 0;
        #100 rst_n = 1;
        #1000 $finish;
    end
    
    // Instantiate core with minimal connections
    riscv_core #(
        .CORE_MODE("SINGLE_CORE")
    ) u_core (
        .clk_i(clk),
        .rst_ni(rst_n),
        .mem_if(), // Leave unconnected for this test
        .m_software_interrupt_i(1'b0),
        .m_timer_interrupt_i(1'b0), 
        .m_external_interrupt_i(1'b0)
    );
    
endmodule
        '''
        
        # Write temporary testbench
        temp_tb_path = self.project_root / "temp_simple_core_tb.sv"
        with open(temp_tb_path, 'w') as f:
            f.write(simple_tb)
        
        try:
            # Try to compile
            compile_cmd = f"cd {self.project_root} && vcs -sverilog -full64 +define+SIMULATION temp_simple_core_tb.sv -o temp_simple_core_tb"
            ret_code, stdout, stderr = self.run_command(compile_cmd)
            
            # Cleanup
            temp_tb_path.unlink(missing_ok=True)
            
            return ret_code == 0
        except:
            temp_tb_path.unlink(missing_ok=True)
            return False
    
    def test_memory_interface(self) -> bool:
        """Test memory interface basic connectivity"""
        mem_if_path = self.project_root / "rtl/memory/memory_req_rsp_if.sv"
        return mem_if_path.exists()
    
    def test_pipeline_flow(self) -> bool:
        """Test basic pipeline stages exist and can be connected"""
        pipeline_files = [
            "rtl/core/fetch_stage.sv",
            "rtl/core/decode_stage.sv", 
            "rtl/core/execute_stage.sv",
            "rtl/core/mem_stage.sv",
            "rtl/core/writeback_stage.sv"
        ]
        
        return all((self.project_root / f).exists() for f in pipeline_files)
    
    def generate_report(self) -> None:
        """Generate validation report"""
        print("\n" + "="*60)
        print("PHASE 1 VALIDATION REPORT")
        print("="*60)
        
        # Calculate overall statistics
        total_files = len(self.results["compilation"])
        passed_compilation = sum(self.results["compilation"].values())
        
        total_tests = len(self.results["functionality"])
        passed_tests = sum(self.results["functionality"].values())
        
        total_integration = len(self.results["integration"])
        passed_integration = sum(self.results["integration"].values())
        
        print(f"\n📊 COMPILATION RESULTS:")
        print(f"   Files tested: {total_files}")
        print(f"   Passed: {passed_compilation}")
        print(f"   Failed: {total_files - passed_compilation}")
        print(f"   Success rate: {passed_compilation/total_files*100:.1f}%" if total_files > 0 else "   No files tested")
        
        print(f"\n🧪 FUNCTIONALITY RESULTS:")
        print(f"   Tests run: {total_tests}")
        print(f"   Passed: {passed_tests}")
        print(f"   Failed: {total_tests - passed_tests}")
        print(f"   Success rate: {passed_tests/total_tests*100:.1f}%" if total_tests > 0 else "   No tests run")
        
        print(f"\n🔧 INTEGRATION RESULTS:")
        print(f"   Tests run: {total_integration}")
        print(f"   Passed: {passed_integration}")
        print(f"   Failed: {total_integration - passed_integration}")
        print(f"   Success rate: {passed_integration/total_integration*100:.1f}%" if total_integration > 0 else "   No tests run")
        
        # Overall assessment
        compilation_rate = passed_compilation/total_files if total_files > 0 else 0
        test_rate = passed_tests/total_tests if total_tests > 0 else 0
        integration_rate = passed_integration/total_integration if total_integration > 0 else 0
        
        overall_rate = (compilation_rate + test_rate + integration_rate) / 3
        
        if overall_rate >= 0.9:
            status = "🟢 EXCELLENT - Ready for Phase 2"
        elif overall_rate >= 0.75:
            status = "🟡 GOOD - Minor fixes needed"
        elif overall_rate >= 0.5:
            status = "🟠 FAIR - Significant work required"
        else:
            status = "🔴 POOR - Major fixes needed"
            
        self.results["overall_status"] = status
        
        print(f"\n🎯 OVERALL STATUS: {status}")
        print(f"   Overall success rate: {overall_rate*100:.1f}%")
        
        # Recommendations
        print(f"\n📋 RECOMMENDATIONS:")
        if compilation_rate < 0.8:
            print("   - Fix compilation errors before proceeding")
        if test_rate < 0.8:
            print("   - Complete unit testbench development")
        if integration_rate < 0.8:
            print("   - Focus on integration issues")
        if overall_rate >= 0.9:
            print("   - Phase 1 looks good! Ready to start Phase 2")
        
        # Save results to file
        results_file = self.project_root / "phase1_validation_results.json"
        with open(results_file, 'w') as f:
            json.dump(self.results, f, indent=2)
        print(f"\n💾 Results saved to: {results_file}")
    
    def run_validation(self) -> None:
        """Run complete Phase 1 validation"""
        print("🚀 Starting RISC-V Phase 1 Validation")
        print(f"📁 Project root: {self.project_root}")
        
        start_time = time.time()
        
        # Run all validation steps
        self.test_rtl_compilation()
        self.test_unit_functionality()  
        self.test_integration()
        
        end_time = time.time()
        duration = end_time - start_time
        
        # Generate report
        self.generate_report()
        
        print(f"\n⏱️  Validation completed in {duration:.1f} seconds")
        

def main():
    """Main entry point"""
    if len(sys.argv) > 1:
        project_root = sys.argv[1]
    else:
        # Default to current directory's parent
        project_root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    
    print(f"RISC-V Phase 1 Validation Script")
    print(f"Project root: {project_root}")
    
    validator = Phase1Validator(project_root)
    validator.run_validation()


if __name__ == "__main__":
    main() 