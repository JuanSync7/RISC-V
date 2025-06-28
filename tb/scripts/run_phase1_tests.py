#!/usr/bin/env python3
"""
Phase 1 Integration and Testing Script
=====================================

This script automates the execution of Phase 1 tests for the RISC-V RV32IM core.
It runs unit tests, integration tests, and generates comprehensive reports.

Author: DesignAI (designai@sondrel.com)
Created: 2025-06-28
"""

import os
import sys
import subprocess
import time
import json
import argparse
from datetime import datetime
from pathlib import Path

class Phase1TestRunner:
    """Phase 1 test runner with comprehensive reporting."""
    
    def __init__(self, project_root, simulator="vcs"):
        self.project_root = Path(project_root)
        self.tb_dir = self.project_root / "tb"
        self.simulator = simulator
        self.results = {
            "timestamp": datetime.now().isoformat(),
            "simulator": simulator,
            "tests": {},
            "summary": {
                "total_tests": 0,
                "passed": 0,
                "failed": 0,
                "performance_targets": {}
            }
        }
        
    def run_command(self, command, cwd=None, timeout=300):
        """Run a command and return results."""
        try:
            result = subprocess.run(
                command,
                shell=True,
                cwd=cwd or self.tb_dir,
                capture_output=True,
                text=True,
                timeout=timeout
            )
            return {
                "returncode": result.returncode,
                "stdout": result.stdout,
                "stderr": result.stderr,
                "success": result.returncode == 0
            }
        except subprocess.TimeoutExpired:
            return {
                "returncode": -1,
                "stdout": "",
                "stderr": "Command timed out",
                "success": False
            }
        except Exception as e:
            return {
                "returncode": -1,
                "stdout": "",
                "stderr": str(e),
                "success": False
            }
    
    def run_unit_tests(self):
        """Run all unit tests for Phase 1 components."""
        print("=" * 60)
        print("PHASE 1 UNIT TESTS")
        print("=" * 60)
        
        unit_tests = [
            ("branch_predictor", "bp_test"),
            ("exception_handler", "exception_handler_test"),
            ("icache", "icache_test"),
            ("alu", "alu_test"),
            ("reg_file", "reg_test")
        ]
        
        for test_name, make_target in unit_tests:
            print(f"\nRunning {test_name} test...")
            start_time = time.time()
            
            # Compile and run test
            compile_cmd = f"make {make_target} SIMULATOR={self.simulator}"
            result = self.run_command(compile_cmd)
            
            end_time = time.time()
            duration = end_time - start_time
            
            # Parse results
            test_result = {
                "duration": duration,
                "success": result["success"],
                "stdout": result["stdout"],
                "stderr": result["stderr"]
            }
            
            # Extract performance metrics if available
            if "PASS" in result["stdout"]:
                test_result["status"] = "PASS"
                self.results["summary"]["passed"] += 1
                print(f"✅ {test_name} test PASSED ({duration:.2f}s)")
            else:
                test_result["status"] = "FAIL"
                self.results["summary"]["failed"] += 1
                print(f"❌ {test_name} test FAILED ({duration:.2f}s)")
            
            self.results["tests"][test_name] = test_result
            self.results["summary"]["total_tests"] += 1
    
    def run_integration_tests(self):
        """Run integration tests for Phase 1."""
        print("\n" + "=" * 60)
        print("PHASE 1 INTEGRATION TESTS")
        print("=" * 60)
        
        print("\nRunning full core integration test...")
        start_time = time.time()
        
        # Compile and run integration test
        compile_cmd = f"make integration_test SIMULATOR={self.simulator}"
        result = self.run_command(compile_cmd)
        
        end_time = time.time()
        duration = end_time - start_time
        
        # Parse integration test results
        integration_result = {
            "duration": duration,
            "success": result["success"],
            "stdout": result["stdout"],
            "stderr": result["stderr"]
        }
        
        # Extract performance metrics
        performance_metrics = self.extract_performance_metrics(result["stdout"])
        integration_result["performance"] = performance_metrics
        
        if "PASS" in result["stdout"] or result["success"]:
            integration_result["status"] = "PASS"
            self.results["summary"]["passed"] += 1
            print(f"✅ Integration test PASSED ({duration:.2f}s)")
        else:
            integration_result["status"] = "FAIL"
            self.results["summary"]["failed"] += 1
            print(f"❌ Integration test FAILED ({duration:.2f}s)")
        
        self.results["tests"]["integration"] = integration_result
        self.results["summary"]["total_tests"] += 1
        
        # Store performance targets
        self.results["summary"]["performance_targets"] = performance_metrics
    
    def extract_performance_metrics(self, output):
        """Extract performance metrics from test output."""
        metrics = {
            "ipc": 0.0,
            "cache_hit_rate": 0.0,
            "branch_prediction_accuracy": 0.0,
            "pipeline_efficiency": 0.0
        }
        
        lines = output.split('\n')
        for line in lines:
            if "IPC:" in line:
                try:
                    metrics["ipc"] = float(line.split("IPC:")[1].strip())
                except:
                    pass
            elif "Cache Hit Rate:" in line:
                try:
                    metrics["cache_hit_rate"] = float(line.split("Cache Hit Rate:")[1].strip().rstrip('%'))
                except:
                    pass
            elif "Branch prediction accuracy" in line:
                try:
                    metrics["branch_prediction_accuracy"] = float(line.split("accuracy")[1].strip().rstrip('%'))
                except:
                    pass
            elif "Pipeline efficiency" in line:
                try:
                    metrics["pipeline_efficiency"] = float(line.split("efficiency")[1].strip().rstrip('%'))
                except:
                    pass
        
        return metrics
    
    def run_coverage_analysis(self):
        """Run coverage analysis for Phase 1 components."""
        print("\n" + "=" * 60)
        print("COVERAGE ANALYSIS")
        print("=" * 60)
        
        print("\nRunning coverage analysis...")
        start_time = time.time()
        
        # Run tests with coverage
        coverage_cmd = f"make coverage SIMULATOR={self.simulator}"
        result = self.run_command(coverage_cmd)
        
        end_time = time.time()
        duration = end_time - start_time
        
        coverage_result = {
            "duration": duration,
            "success": result["success"],
            "stdout": result["stdout"],
            "stderr": result["stderr"]
        }
        
        # Extract coverage metrics
        coverage_metrics = self.extract_coverage_metrics(result["stdout"])
        coverage_result["metrics"] = coverage_metrics
        
        if result["success"]:
            coverage_result["status"] = "PASS"
            print(f"✅ Coverage analysis completed ({duration:.2f}s)")
        else:
            coverage_result["status"] = "FAIL"
            print(f"❌ Coverage analysis failed ({duration:.2f}s)")
        
        self.results["tests"]["coverage"] = coverage_result
        self.results["summary"]["total_tests"] += 1
    
    def extract_coverage_metrics(self, output):
        """Extract coverage metrics from output."""
        metrics = {
            "line_coverage": 0.0,
            "branch_coverage": 0.0,
            "expression_coverage": 0.0,
            "functional_coverage": 0.0
        }
        
        lines = output.split('\n')
        for line in lines:
            if "Line Coverage" in line:
                try:
                    metrics["line_coverage"] = float(line.split(":")[1].strip().rstrip('%'))
                except:
                    pass
            elif "Branch Coverage" in line:
                try:
                    metrics["branch_coverage"] = float(line.split(":")[1].strip().rstrip('%'))
                except:
                    pass
            elif "Expression Coverage" in line:
                try:
                    metrics["expression_coverage"] = float(line.split(":")[1].strip().rstrip('%'))
                except:
                    pass
            elif "Functional Coverage" in line:
                try:
                    metrics["functional_coverage"] = float(line.split(":")[1].strip().rstrip('%'))
                except:
                    pass
        
        return metrics
    
    def generate_report(self):
        """Generate comprehensive test report."""
        print("\n" + "=" * 60)
        print("PHASE 1 TEST REPORT")
        print("=" * 60)
        
        # Calculate summary statistics
        total = self.results["summary"]["total_tests"]
        passed = self.results["summary"]["passed"]
        failed = self.results["summary"]["failed"]
        success_rate = (passed / total * 100) if total > 0 else 0
        
        print(f"\nTest Summary:")
        print(f"  Total Tests: {total}")
        print(f"  Passed: {passed}")
        print(f"  Failed: {failed}")
        print(f"  Success Rate: {success_rate:.1f}%")
        
        # Performance targets
        if "performance_targets" in self.results["summary"]:
            perf = self.results["summary"]["performance_targets"]
            print(f"\nPerformance Targets:")
            print(f"  IPC: {perf.get('ipc', 0):.2f} (target: ≥0.8)")
            print(f"  Cache Hit Rate: {perf.get('cache_hit_rate', 0):.1f}% (target: ≥85%)")
            print(f"  Branch Prediction Accuracy: {perf.get('branch_prediction_accuracy', 0):.1f}% (target: ≥85%)")
            print(f"  Pipeline Efficiency: {perf.get('pipeline_efficiency', 0):.1f}% (target: ≥70%)")
        
        # Coverage summary
        if "coverage" in self.results["tests"]:
            cov = self.results["tests"]["coverage"]["metrics"]
            print(f"\nCoverage Summary:")
            print(f"  Line Coverage: {cov.get('line_coverage', 0):.1f}% (target: ≥95%)")
            print(f"  Branch Coverage: {cov.get('branch_coverage', 0):.1f}% (target: ≥90%)")
            print(f"  Expression Coverage: {cov.get('expression_coverage', 0):.1f}% (target: ≥85%)")
            print(f"  Functional Coverage: {cov.get('functional_coverage', 0):.1f}% (target: ≥90%)")
        
        # Save detailed report
        report_file = self.tb_dir / "phase1_test_report.json"
        with open(report_file, 'w') as f:
            json.dump(self.results, f, indent=2)
        
        print(f"\nDetailed report saved to: {report_file}")
        
        # Generate summary report
        self.generate_summary_report()
    
    def generate_summary_report(self):
        """Generate a human-readable summary report."""
        report_file = self.tb_dir / "phase1_summary_report.txt"
        
        with open(report_file, 'w') as f:
            f.write("=" * 60 + "\n")
            f.write("PHASE 1 INTEGRATION TEST SUMMARY\n")
            f.write("=" * 60 + "\n")
            f.write(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
            f.write(f"Simulator: {self.simulator}\n\n")
            
            # Test summary
            total = self.results["summary"]["total_tests"]
            passed = self.results["summary"]["passed"]
            failed = self.results["summary"]["failed"]
            success_rate = (passed / total * 100) if total > 0 else 0
            
            f.write("TEST SUMMARY:\n")
            f.write(f"  Total Tests: {total}\n")
            f.write(f"  Passed: {passed}\n")
            f.write(f"  Failed: {failed}\n")
            f.write(f"  Success Rate: {success_rate:.1f}%\n\n")
            
            # Individual test results
            f.write("INDIVIDUAL TEST RESULTS:\n")
            for test_name, test_result in self.results["tests"].items():
                status = test_result.get("status", "UNKNOWN")
                duration = test_result.get("duration", 0)
                f.write(f"  {test_name}: {status} ({duration:.2f}s)\n")
            
            f.write("\n")
            
            # Performance targets
            if "performance_targets" in self.results["summary"]:
                perf = self.results["summary"]["performance_targets"]
                f.write("PERFORMANCE TARGETS:\n")
                f.write(f"  IPC: {perf.get('ipc', 0):.2f} (target: ≥0.8)\n")
                f.write(f"  Cache Hit Rate: {perf.get('cache_hit_rate', 0):.1f}% (target: ≥85%)\n")
                f.write(f"  Branch Prediction Accuracy: {perf.get('branch_prediction_accuracy', 0):.1f}% (target: ≥85%)\n")
                f.write(f"  Pipeline Efficiency: {perf.get('pipeline_efficiency', 0):.1f}% (target: ≥70%)\n\n")
            
            # Coverage summary
            if "coverage" in self.results["tests"]:
                cov = self.results["tests"]["coverage"]["metrics"]
                f.write("COVERAGE SUMMARY:\n")
                f.write(f"  Line Coverage: {cov.get('line_coverage', 0):.1f}% (target: ≥95%)\n")
                f.write(f"  Branch Coverage: {cov.get('branch_coverage', 0):.1f}% (target: ≥90%)\n")
                f.write(f"  Expression Coverage: {cov.get('expression_coverage', 0):.1f}% (target: ≥85%)\n")
                f.write(f"  Functional Coverage: {cov.get('functional_coverage', 0):.1f}% (target: ≥90%)\n\n")
            
            # Phase 1 completion status
            f.write("PHASE 1 COMPLETION STATUS:\n")
            if success_rate >= 90 and perf.get('ipc', 0) >= 0.8 and perf.get('cache_hit_rate', 0) >= 85:
                f.write("  ✅ PHASE 1 COMPLETED SUCCESSFULLY\n")
                f.write("  All performance targets met\n")
                f.write("  Ready for Phase 2 development\n")
            else:
                f.write("  ⚠️  PHASE 1 NEEDS IMPROVEMENT\n")
                if success_rate < 90:
                    f.write("  - Test success rate below target\n")
                if perf.get('ipc', 0) < 0.8:
                    f.write("  - IPC below target\n")
                if perf.get('cache_hit_rate', 0) < 85:
                    f.write("  - Cache hit rate below target\n")
        
        print(f"Summary report saved to: {report_file}")
    
    def run_all_tests(self):
        """Run complete Phase 1 test suite."""
        print("Starting Phase 1 Integration and Testing")
        print("=" * 60)
        
        start_time = time.time()
        
        try:
            # Run unit tests
            self.run_unit_tests()
            
            # Run integration tests
            self.run_integration_tests()
            
            # Run coverage analysis
            self.run_coverage_analysis()
            
            # Generate reports
            self.generate_report()
            
        except KeyboardInterrupt:
            print("\nTest execution interrupted by user")
            return False
        except Exception as e:
            print(f"\nTest execution failed: {e}")
            return False
        
        end_time = time.time()
        total_duration = end_time - start_time
        
        print(f"\nPhase 1 testing completed in {total_duration:.2f} seconds")
        
        # Return success if all tests passed
        total = self.results["summary"]["total_tests"]
        passed = self.results["summary"]["passed"]
        return passed == total and total > 0

def main():
    """Main function."""
    parser = argparse.ArgumentParser(description="Phase 1 Integration and Testing Script")
    parser.add_argument("--project-root", default=".", help="Project root directory")
    parser.add_argument("--simulator", default="vcs", choices=["vcs", "modelsim"], help="Simulator to use")
    parser.add_argument("--unit-only", action="store_true", help="Run only unit tests")
    parser.add_argument("--integration-only", action="store_true", help="Run only integration tests")
    parser.add_argument("--coverage-only", action="store_true", help="Run only coverage analysis")
    
    args = parser.parse_args()
    
    # Create test runner
    runner = Phase1TestRunner(args.project_root, args.simulator)
    
    # Run tests based on arguments
    if args.unit_only:
        runner.run_unit_tests()
        runner.generate_report()
    elif args.integration_only:
        runner.run_integration_tests()
        runner.generate_report()
    elif args.coverage_only:
        runner.run_coverage_analysis()
        runner.generate_report()
    else:
        success = runner.run_all_tests()
        sys.exit(0 if success else 1)

if __name__ == "__main__":
    main() 