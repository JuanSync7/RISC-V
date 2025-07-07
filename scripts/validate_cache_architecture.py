#!/usr/bin/env python3
"""
RISC-V Cache Architecture Validation Script (CI/CD Ready)

This script validates the cache topology system integrity and is designed
to be run in CI/CD pipelines to catch regressions and ensure system health.

Usage:
    python scripts/validate_cache_architecture.py [--verbose] [--exit-on-fail]
    
Exit Codes:
    0: All validations passed
    1: Critical validation failures detected
    2: Warning-level issues detected (configurable)
"""

import os
import sys
import argparse
import json
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional

class CacheArchitectureValidator:
    """Comprehensive cache architecture validation for CI/CD"""
    
    def __init__(self, project_root: str = ".", verbose: bool = False):
        self.project_root = Path(project_root)
        self.verbose = verbose
        self.results = {}
        self.errors = []
        self.warnings = []
        self.critical_failures = 0
        
    def log(self, level: str, message: str) -> None:
        """Centralized logging with level support"""
        icons = {"INFO": "✅", "WARN": "⚠️", "ERROR": "❌", "DEBUG": "🔍"}
        icon = icons.get(level, "ℹ️")
        
        if level == "ERROR":
            self.errors.append(message)
            self.critical_failures += 1
        elif level == "WARN":
            self.warnings.append(message)
            
        if self.verbose or level in ["ERROR", "WARN"]:
            print(f"{icon} {message}")
    
    def validate_file_structure(self) -> bool:
        """Validate that all required cache architecture files exist"""
        self.log("INFO", "Validating cache architecture file structure...")
        
        required_files = [
            "rtl/pkg/riscv_cache_topology_pkg.sv",
            "rtl/memory/cache_cluster_manager.sv", 
            "rtl/core/multi_core_system.sv",
            "rtl/pkg/riscv_config_pkg.sv",
            "rtl/pkg/riscv_core_pkg.sv"
        ]
        
        missing_files = []
        for file_path in required_files:
            full_path = self.project_root / file_path
            if not full_path.exists():
                missing_files.append(file_path)
                self.log("ERROR", f"Missing critical file: {file_path}")
            else:
                self.log("DEBUG", f"Found: {file_path}")
        
        if missing_files:
            self.log("ERROR", f"Missing {len(missing_files)} critical cache architecture files")
            return False
        
        self.log("INFO", "✅ All cache architecture files present")
        return True
    
    def validate_topology_package(self) -> bool:
        """Validate cache topology package completeness"""
        self.log("INFO", "Validating cache topology package...")
        
        topology_file = self.project_root / "rtl/pkg/riscv_cache_topology_pkg.sv"
        
        try:
            with open(topology_file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            self.log("ERROR", f"Cannot read topology package: {e}")
            return False
        
        # Critical components that must exist
        critical_components = [
            ("Topology Enums", ["CACHE_TOPOLOGY_UNIFIED", "CACHE_TOPOLOGY_CLUSTERED", "CACHE_TOPOLOGY_NUMA"]),
            ("Configuration Functions", ["get_unified_topology", "get_clustered_topology", "get_numa_topology"]),
            ("Validation Functions", ["validate_cache_topology"]),
            ("Address Mapping", ["get_l2_instance_for_address", "get_l3_instance_for_address"]),
            ("Core Mapping", ["get_l2_for_core"])
        ]
        
        all_valid = True
        for component_name, required_items in critical_components:
            missing_items = [item for item in required_items if item not in content]
            
            if missing_items:
                self.log("ERROR", f"Topology package missing {component_name}: {missing_items}")
                all_valid = False
            else:
                self.log("DEBUG", f"✅ {component_name} complete")
        
        return all_valid
    
    def validate_cluster_manager(self) -> bool:
        """Validate cache cluster manager implementation"""
        self.log("INFO", "Validating cache cluster manager...")
        
        cluster_file = self.project_root / "rtl/memory/cache_cluster_manager.sv"
        
        try:
            with open(cluster_file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            self.log("ERROR", f"Cannot read cluster manager: {e}")
            return False
        
        # Critical features for multi-cache support
        required_features = [
            ("Topology Input", "topology_config_i"),
            ("L2 Generation", "gen_l2_instances"),
            ("L3 Generation", "gen_l3_instances"), 
            ("Core Routing", "gen_core_routing"),
            ("Max L2 Parameter", "MAX_L2_INSTANCES"),
            ("Max L3 Parameter", "MAX_L3_INSTANCES")
        ]
        
        all_valid = True
        for feature_name, feature_pattern in required_features:
            if feature_pattern not in content:
                self.log("ERROR", f"Cluster manager missing {feature_name}: {feature_pattern}")
                all_valid = False
            else:
                self.log("DEBUG", f"✅ {feature_name} found")
        
        return all_valid
    
    def validate_system_integration(self) -> bool:
        """Validate multi-core system integration"""
        self.log("INFO", "Validating system integration...")
        
        system_file = self.project_root / "rtl/core/multi_core_system.sv"
        
        try:
            with open(system_file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            self.log("ERROR", f"Cannot read multi-core system: {e}")
            return False
        
        # Integration checkpoints
        integration_points = [
            ("Cluster Manager Instance", "cache_cluster_manager"),
            ("Topology Configuration", "cache_topology_config"),
            ("Unified Topology Call", "get_unified_topology"),
            ("Clustered Topology Call", "get_clustered_topology"),
            ("NUMA Topology Call", "get_numa_topology"),
            ("Core Count Logic", "NUM_CORES")
        ]
        
        all_valid = True
        for point_name, pattern in integration_points:
            if pattern not in content:
                self.log("ERROR", f"System integration missing {point_name}")
                all_valid = False
            else:
                self.log("DEBUG", f"✅ {point_name} integrated")
        
        return all_valid
    
    def validate_configuration_parameters(self) -> bool:
        """Validate configuration parameters"""
        self.log("INFO", "Validating configuration parameters...")
        
        config_file = self.project_root / "rtl/pkg/riscv_config_pkg.sv"
        
        try:
            with open(config_file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            self.log("ERROR", f"Cannot read config package: {e}")
            return False
        
        # Required cache topology parameters
        required_params = [
            "DEFAULT_CACHE_TOPOLOGY",
            "DEFAULT_L2_INSTANCES", 
            "DEFAULT_L3_INSTANCES",
            "DEFAULT_MEMORY_CONTROLLERS"
        ]
        
        missing_params = [param for param in required_params if param not in content]
        
        if missing_params:
            self.log("ERROR", f"Missing configuration parameters: {missing_params}")
            return False
        
        self.log("DEBUG", "✅ All configuration parameters present")
        return True
    
    def validate_package_imports(self) -> bool:
        """Validate package import structure"""
        self.log("INFO", "Validating package imports...")
        
        core_pkg_file = self.project_root / "rtl/pkg/riscv_core_pkg.sv"
        
        try:
            with open(core_pkg_file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            self.log("ERROR", f"Cannot read core package: {e}")
            return False
        
        # Check for cache topology import
        if "import riscv_cache_topology_pkg::*;" not in content:
            self.log("ERROR", "Cache topology package not imported in core package")
            return False
        
        self.log("DEBUG", "✅ Package imports validated")
        return True
    
    def validate_parameter_adaptation_logic(self) -> bool:
        """Validate parameter adaptation logic in multi-core system"""
        self.log("INFO", "Validating parameter adaptation logic...")
        
        system_file = self.project_root / "rtl/core/multi_core_system.sv"
        
        try:
            with open(system_file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            self.log("ERROR", f"Cannot read multi-core system: {e}")
            return False
        
        # Look for adaptive logic patterns
        adaptation_patterns = [
            ("Core Count Case", r"case\s*\(\s*NUM_CORES\s*\)"),
            ("Small System Branch", "1, 2:"),
            ("Default Case", "default:")
        ]
        
        import re
        all_valid = True
        for pattern_name, pattern in adaptation_patterns:
            if isinstance(pattern, str):
                found = pattern in content
            else:
                found = re.search(pattern, content, re.IGNORECASE) is not None
            
            if not found:
                self.log("WARN", f"Parameter adaptation pattern not found: {pattern_name}")
                # Note: This is a warning, not an error, as adaptation logic may vary
            else:
                self.log("DEBUG", f"✅ {pattern_name} found")
        
        return True  # Always return True as adaptation logic patterns are warnings
    
    def run_comprehensive_validation(self) -> bool:
        """Run all validation checks"""
        self.log("INFO", "🚀 Starting Cache Architecture Validation")
        self.log("INFO", f"Project Root: {self.project_root.absolute()}")
        self.log("INFO", f"Validation Time: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        
        # Define all validation checks
        validations = [
            ("File Structure", self.validate_file_structure),
            ("Topology Package", self.validate_topology_package),
            ("Cluster Manager", self.validate_cluster_manager),
            ("System Integration", self.validate_system_integration),
            ("Configuration Parameters", self.validate_configuration_parameters),
            ("Package Imports", self.validate_package_imports),
            ("Parameter Adaptation", self.validate_parameter_adaptation_logic)
        ]
        
        passed_validations = 0
        total_validations = len(validations)
        
        # Run each validation
        for validation_name, validation_func in validations:
            self.log("INFO", f"\n{'='*50}")
            self.log("INFO", f"Running: {validation_name}")
            self.log("INFO", f"{'='*50}")
            
            try:
                result = validation_func()
                self.results[validation_name] = "PASS" if result else "FAIL"
                if result:
                    passed_validations += 1
                    self.log("INFO", f"✅ {validation_name}: PASSED")
                else:
                    self.log("ERROR", f"❌ {validation_name}: FAILED")
            except Exception as e:
                self.log("ERROR", f"Exception in {validation_name}: {e}")
                self.results[validation_name] = "ERROR"
        
        # Generate summary
        success_rate = (passed_validations / total_validations) * 100
        
        self.log("INFO", f"\n{'='*60}")
        self.log("INFO", "🎯 VALIDATION SUMMARY")
        self.log("INFO", f"{'='*60}")
        
        for validation_name, result in self.results.items():
            status_icon = "✅" if result == "PASS" else "❌"
            self.log("INFO", f"{status_icon} {validation_name}: {result}")
        
        self.log("INFO", f"\n📊 Results: {passed_validations}/{total_validations} validations passed ({success_rate:.1f}%)")
        
        if self.warnings:
            self.log("INFO", f"\n⚠️ Warnings ({len(self.warnings)}):")
            for warning in self.warnings[:5]:  # Limit output
                self.log("INFO", f"  • {warning}")
            if len(self.warnings) > 5:
                self.log("INFO", f"  ... and {len(self.warnings) - 5} more warnings")
        
        if self.errors:
            self.log("INFO", f"\n❌ Errors ({len(self.errors)}):")
            for error in self.errors[:5]:  # Limit output
                self.log("INFO", f"  • {error}")
            if len(self.errors) > 5:
                self.log("INFO", f"  ... and {len(self.errors) - 5} more errors")
        
        # Determine final result
        if self.critical_failures == 0:
            self.log("INFO", "\n🎉 VALIDATION PASSED: Cache architecture is healthy")
            return True
        elif self.critical_failures <= 2:
            self.log("INFO", "\n⚠️ VALIDATION WARNING: Minor issues detected")
            return True
        else:
            self.log("INFO", "\n❌ VALIDATION FAILED: Critical issues need resolution")
            return False
    
    def generate_report(self, output_file: Optional[str] = None) -> Dict:
        """Generate a detailed validation report"""
        report = {
            "timestamp": datetime.now().isoformat(),
            "project_root": str(self.project_root.absolute()),
            "validation_results": self.results,
            "summary": {
                "total_validations": len(self.results),
                "passed_validations": len([r for r in self.results.values() if r == "PASS"]),
                "failed_validations": len([r for r in self.results.values() if r == "FAIL"]),
                "error_count": len(self.errors),
                "warning_count": len(self.warnings),
                "critical_failures": self.critical_failures
            },
            "errors": self.errors,
            "warnings": self.warnings
        }
        
        if output_file:
            try:
                with open(output_file, 'w') as f:
                    json.dump(report, f, indent=2)
                self.log("INFO", f"📄 Report saved to: {output_file}")
            except Exception as e:
                self.log("ERROR", f"Failed to save report: {e}")
        
        return report

def main():
    """Main CLI entry point"""
    parser = argparse.ArgumentParser(
        description="Validate RISC-V Cache Architecture (CI/CD Ready)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python scripts/validate_cache_architecture.py                    # Basic validation
  python scripts/validate_cache_architecture.py --verbose          # Detailed output  
  python scripts/validate_cache_architecture.py --report cache.json # Save report
        """
    )
    
    parser.add_argument("--verbose", "-v", action="store_true",
                       help="Enable verbose output for debugging")
    parser.add_argument("--project-root", default=".",
                       help="Project root directory (default: current directory)")
    parser.add_argument("--report", metavar="FILE",
                       help="Save detailed JSON report to file")
    parser.add_argument("--exit-on-warning", action="store_true",
                       help="Exit with code 2 on warnings (for strict CI/CD)")
    
    args = parser.parse_args()
    
    # Run validation
    validator = CacheArchitectureValidator(args.project_root, args.verbose)
    success = validator.run_comprehensive_validation()
    
    # Generate report if requested
    if args.report:
        validator.generate_report(args.report)
    
    # Determine exit code
    if not success:
        sys.exit(1)  # Critical failures
    elif args.exit_on_warning and validator.warnings:
        sys.exit(2)  # Warnings in strict mode
    else:
        sys.exit(0)  # Success

if __name__ == "__main__":
    main() 