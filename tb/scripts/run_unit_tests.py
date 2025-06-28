#!/usr/bin/env python3
"""
RISC-V Unit Test Runner

This script automates the compilation and execution of unit testbenches
for the RISC-V RV32IM core project.

Author: DesignAI (designai@sondrel.com)
Created: 2025-06-28
"""

import os
import sys
import subprocess
import argparse
import time
import json
from pathlib import Path
from typing import List, Dict, Any

class TestRunner:
    """Test runner for RISC-V unit tests."""
    
    def __init__(self, project_root: str, simulator: str = "vcs"):
        self.project_root = Path(project_root)
        self.simulator = simulator
        self.tb_dir = self.project_root / "tb"
        self.rtl_dir = self.project_root / "rtl"
        self.results = {}
        
    def find_testbenches(self) -> List[Path]:
        """Find all unit testbenches in the project."""
        testbenches = []
        unit_dir = self.tb_dir / "unit"
        
        if unit_dir.exists():
            for tb_file in unit_dir.rglob("*_tb.sv"):
                testbenches.append(tb_file)
                
        return sorted(testbenches)
    
    def create_filelist(self, testbench: Path) -> Path:
        """Create a filelist for the given testbench."""
        filelist_path = testbench.parent / f"{testbench.stem}.f"
        
        files = [
            # Common utilities
            str(self.tb_dir / "common" / "test_utils.sv"),
            # RTL files (add specific dependencies based on testbench)
            str(self.rtl_dir / "core" / "riscv_core_pkg.sv"),
        ]
        
        # Add specific RTL files based on testbench name
        if "alu" in testbench.name:
            files.append(str(self.rtl_dir / "units" / "alu.sv"))
        elif "reg_file" in testbench.name:
            files.append(str(self.rtl_dir / "units" / "reg_file.sv"))
        elif "mult_unit" in testbench.name:
            files.append(str(self.rtl_dir / "units" / "mult_unit.sv"))
        elif "div_unit" in testbench.name:
            files.append(str(self.rtl_dir / "units" / "div_unit.sv"))
        elif "csr_regfile" in testbench.name:
            files.append(str(self.rtl_dir / "units" / "csr_regfile.sv"))
        elif "exception_handler" in testbench.name:
            files.append(str(self.rtl_dir / "units" / "exception_handler.sv"))
        elif "hazard_unit" in testbench.name:
            files.append(str(self.rtl_dir / "control" / "hazard_unit.sv"))
        elif "icache" in testbench.name:
            files.append(str(self.rtl_dir / "memory" / "icache.sv"))
        elif "memory_wrapper" in testbench.name:
            files.append(str(self.rtl_dir / "memory" / "memory_wrapper.sv"))
        elif "axi4_adapter" in testbench.name:
            files.append(str(self.rtl_dir / "protocols" / "axi4_adapter.sv"))
        elif "branch_predictor" in testbench.name:
            files.append(str(self.rtl_dir / "prediction" / "branch_predictor.sv"))
        
        # Add the testbench itself
        files.append(str(testbench))
        
        # Write filelist
        with open(filelist_path, 'w') as f:
            for file_path in files:
                if Path(file_path).exists():
                    f.write(f"{file_path}\n")
                else:
                    print(f"Warning: File not found: {file_path}")
        
        return filelist_path
    
    def compile_test(self, testbench: Path) -> bool:
        """Compile a testbench."""
        print(f"Compiling {testbench.name}...")
        
        filelist_path = self.create_filelist(testbench)
        output_name = testbench.stem
        
        if self.simulator == "vcs":
            cmd = [
                "vcs", "-full64", "-sverilog", "-debug_all",
                "-f", str(filelist_path),
                "-o", output_name,
                "+v2k", "+define+SIMULATION"
            ]
        elif self.simulator == "modelsim":
            cmd = [
                "vlog", "-sv", "-f", str(filelist_path)
            ]
        else:
            print(f"Unsupported simulator: {self.simulator}")
            return False
        
        try:
            result = subprocess.run(cmd, capture_output=True, text=True, cwd=testbench.parent)
            if result.returncode == 0:
                print(f"✓ {testbench.name} compiled successfully")
                return True
            else:
                print(f"✗ {testbench.name} compilation failed:")
                print(result.stderr)
                return False
        except FileNotFoundError:
            print(f"✗ Simulator {self.simulator} not found")
            return False
    
    def run_test(self, testbench: Path) -> Dict[str, Any]:
        """Run a compiled testbench."""
        print(f"Running {testbench.name}...")
        
        start_time = time.time()
        
        if self.simulator == "vcs":
            cmd = [f"./{testbench.stem}"]
        elif self.simulator == "modelsim":
            cmd = ["vsim", "-c", "-do", "run -all; quit", testbench.stem]
        else:
            return {"status": "error", "message": f"Unsupported simulator: {self.simulator}"}
        
        try:
            result = subprocess.run(cmd, capture_output=True, text=True, cwd=testbench.parent, timeout=300)
            end_time = time.time()
            
            if result.returncode == 0:
                # Parse test results from output
                test_stats = self.parse_test_output(result.stdout)
                return {
                    "status": "passed",
                    "duration": end_time - start_time,
                    "stats": test_stats
                }
            else:
                return {
                    "status": "failed",
                    "duration": end_time - start_time,
                    "error": result.stderr
                }
        except subprocess.TimeoutExpired:
            return {
                "status": "timeout",
                "duration": 300,
                "error": "Test timed out after 5 minutes"
            }
        except Exception as e:
            return {
                "status": "error",
                "duration": 0,
                "error": str(e)
            }
    
    def parse_test_output(self, output: str) -> Dict[str, Any]:
        """Parse test statistics from simulation output."""
        stats = {
            "total_tests": 0,
            "passed_tests": 0,
            "failed_tests": 0,
            "timeout_tests": 0,
            "skipped_tests": 0,
            "pass_rate": 0.0
        }
        
        # Look for test summary in output
        lines = output.split('\n')
        for line in lines:
            if "Total Tests:" in line:
                try:
                    stats["total_tests"] = int(line.split(':')[1].strip())
                except:
                    pass
            elif "Passed:" in line:
                try:
                    stats["passed_tests"] = int(line.split(':')[1].strip())
                except:
                    pass
            elif "Failed:" in line:
                try:
                    stats["failed_tests"] = int(line.split(':')[1].strip())
                except:
                    pass
            elif "Pass Rate:" in line:
                try:
                    stats["pass_rate"] = float(line.split(':')[1].strip().replace('%', ''))
                except:
                    pass
        
        return stats
    
    def run_all_tests(self) -> Dict[str, Any]:
        """Run all unit tests."""
        print("=" * 60)
        print("RISC-V UNIT TEST RUNNER")
        print("=" * 60)
        
        testbenches = self.find_testbenches()
        if not testbenches:
            print("No testbenches found!")
            return {}
        
        print(f"Found {len(testbenches)} testbench(es):")
        for tb in testbenches:
            print(f"  - {tb.name}")
        print()
        
        total_start_time = time.time()
        passed = 0
        failed = 0
        
        for testbench in testbenches:
            print(f"\n{'='*40}")
            print(f"Testing: {testbench.name}")
            print(f"{'='*40}")
            
            # Compile test
            if not self.compile_test(testbench):
                self.results[testbench.name] = {
                    "status": "compilation_failed",
                    "duration": 0
                }
                failed += 1
                continue
            
            # Run test
            result = self.run_test(testbench)
            self.results[testbench.name] = result
            
            if result["status"] == "passed":
                passed += 1
                print(f"✓ {testbench.name} PASSED")
            else:
                failed += 1
                print(f"✗ {testbench.name} FAILED: {result.get('error', 'Unknown error')}")
        
        total_duration = time.time() - total_start_time
        
        # Generate summary
        summary = {
            "total_tests": len(testbenches),
            "passed": passed,
            "failed": failed,
            "total_duration": total_duration,
            "results": self.results
        }
        
        self.print_summary(summary)
        self.save_results(summary)
        
        return summary
    
    def print_summary(self, summary: Dict[str, Any]):
        """Print test summary."""
        print("\n" + "=" * 60)
        print("TEST SUMMARY")
        print("=" * 60)
        print(f"Total Testbenches: {summary['total_tests']}")
        print(f"Passed:           {summary['passed']}")
        print(f"Failed:           {summary['failed']}")
        print(f"Total Duration:   {summary['total_duration']:.2f} seconds")
        print(f"Pass Rate:        {(summary['passed']/summary['total_tests']*100):.1f}%")
        
        if summary['failed'] > 0:
            print("\nFailed Tests:")
            for name, result in summary['results'].items():
                if result['status'] != 'passed':
                    print(f"  - {name}: {result['status']}")
        
        print("=" * 60)
    
    def save_results(self, summary: Dict[str, Any]):
        """Save test results to JSON file."""
        results_file = self.tb_dir / "test_results.json"
        with open(results_file, 'w') as f:
            json.dump(summary, f, indent=2)
        print(f"Results saved to: {results_file}")

def main():
    parser = argparse.ArgumentParser(description="RISC-V Unit Test Runner")
    parser.add_argument("--project-root", default=".", help="Project root directory")
    parser.add_argument("--simulator", choices=["vcs", "modelsim"], default="vcs", help="Simulator to use")
    parser.add_argument("--test", help="Run specific testbench")
    
    args = parser.parse_args()
    
    runner = TestRunner(args.project_root, args.simulator)
    
    if args.test:
        # Run specific test
        test_path = Path(args.test)
        if not test_path.exists():
            test_path = runner.tb_dir / "unit" / args.test
        if test_path.exists():
            runner.run_all_tests()
        else:
            print(f"Testbench not found: {args.test}")
            sys.exit(1)
    else:
        # Run all tests
        runner.run_all_tests()

if __name__ == "__main__":
    main() 