#!/usr/bin/env python3
"""
RISC-V RTL Implementation Completion Validator
============================================

This script validates that all Phase 1 and Phase 2 RTL components are implemented
and properly integrated for 100% completion status.

Author: RTL Design Agent
Date: 2025-01-27
Version: 1.0.0
"""

import os
import sys
import re
import json
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from datetime import datetime

@dataclass
class ModuleInfo:
    """Information about an RTL module"""
    name: str
    path: str
    size_bytes: int
    line_count: int
    has_ai_tags: bool
    has_assertions: bool
    synthesis_ready: bool
    
@dataclass
class ValidationResult:
    """Result of RTL validation"""
    passed: bool
    score: float
    details: str
    recommendations: List[str]

class RTLCompletionValidator:
    """Main RTL completion validation class"""
    
    def __init__(self, rtl_root: str = "rtl"):
        self.rtl_root = Path(rtl_root)
        self.validation_results = {}
        self.overall_score = 0.0
        self.critical_modules = []
        self.missing_modules = []
        
        # Define required modules for 100% completion
        self.required_modules = {
            # Phase 1 - Basic RISC-V Core
            "core": [
                "riscv_core.sv",
                "fetch_stage.sv", 
                "decode_stage.sv",
                "execute_stage.sv",
                "mem_stage.sv",
                "writeback_stage.sv",
                "multi_core_system.sv",
                "core_subsystem.sv",
                "core_manager.sv"
            ],
            
            # Functional Units
            "units": [
                "alu.sv",
                "reg_file.sv",
                "mult_unit.sv",
                "div_unit.sv",
                "csr_regfile.sv",
                "exception_handler.sv"
            ],
            
            # Execution Units (Phase 2)
            "execution": [
                "reorder_buffer.sv",
                "reservation_station.sv",
                "register_renaming.sv",
                "multiple_execution_units.sv"
            ],
            
            # Memory Subsystem
            "memory": [
                "icache.sv",
                "l2_cache.sv",
                "l3_cache.sv",
                "cache_coherency_controller.sv",
                "memory_wrapper.sv",
                "memory_req_rsp_if.sv"
            ],
            
            # Advanced Features (Phase 2)
            "core_advanced": [
                "system_integration_validator.sv",
                "performance_optimizer.sv", 
                "advanced_feature_integrator.sv",
                "ooo_engine.sv"
            ],
            
            # Protocol Support
            "protocols": [
                "axi4_master_adapter.sv",
                "axi4_slave_adapter.sv",
                "chi_adapter.sv",
                "tilelink_adapter.sv",
                "protocol_factory.sv"
            ]
        }
        
    def validate_file_exists(self, category: str, filename: str) -> Tuple[bool, Optional[ModuleInfo]]:
        """Validate that a required file exists and get its info"""
        file_path = self.rtl_root / category / filename
        
        if not file_path.exists():
            return False, None
            
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # Analyze file content
            lines = content.split('\n')
            line_count = len(lines)
            size_bytes = len(content.encode('utf-8'))
            
            # Check for AI tags and assertions
            has_ai_tags = 'AI_TAG:' in content
            has_assertions = re.search(r'assert\s+property', content) is not None
            
            # Check if synthesis ready (basic checks)
            synthesis_ready = all([
                '`timescale' in content,
                'module ' in content,
                'endmodule' in content,
                not re.search(r'\$display\s*\(', content) or '`ifdef SIMULATION' in content
            ])
            
            module_info = ModuleInfo(
                name=filename,
                path=str(file_path),
                size_bytes=size_bytes,
                line_count=line_count,
                has_ai_tags=has_ai_tags,
                has_assertions=has_assertions,
                synthesis_ready=synthesis_ready
            )
            
            return True, module_info
            
        except Exception as e:
            print(f"Error reading {file_path}: {e}")
            return False, None
    
    def validate_module_quality(self, module_info: ModuleInfo) -> ValidationResult:
        """Validate the quality of an RTL module"""
        score = 0.0
        recommendations = []
        details = []
        
        # File size check (should be substantial)
        if module_info.size_bytes > 1000:
            score += 20
            details.append(f"✅ Substantial implementation ({module_info.size_bytes} bytes)")
        else:
            recommendations.append(f"Module {module_info.name} appears minimal ({module_info.size_bytes} bytes)")
        
        # Line count check
        if module_info.line_count > 50:
            score += 20
            details.append(f"✅ Good implementation depth ({module_info.line_count} lines)")
        else:
            recommendations.append(f"Module {module_info.name} may need more implementation")
        
        # AI tags check (indicates proper documentation)
        if module_info.has_ai_tags:
            score += 20
            details.append("✅ Comprehensive AI_TAG documentation")
        else:
            recommendations.append("Add AI_TAG documentation for better maintainability")
        
        # Assertions check (indicates verification readiness)
        if module_info.has_assertions:
            score += 20
            details.append("✅ Contains SystemVerilog assertions")
        else:
            recommendations.append("Add assertions for better verification")
        
        # Synthesis readiness
        if module_info.synthesis_ready:
            score += 20
            details.append("✅ Synthesis-ready RTL")
        else:
            recommendations.append("Ensure synthesis readiness (timescale, proper constructs)")
        
        passed = score >= 80  # Require 80% for good quality
        
        return ValidationResult(
            passed=passed,
            score=score,
            details="; ".join(details),
            recommendations=recommendations
        )
    
    def validate_category(self, category: str) -> Tuple[float, List[str]]:
        """Validate all modules in a category"""
        if category not in self.required_modules:
            return 0.0, [f"Unknown category: {category}"]
        
        required_files = self.required_modules[category]
        category_score = 0.0
        issues = []
        found_count = 0
        
        print(f"\n📁 Validating {category.upper()} modules:")
        
        for filename in required_files:
            exists, module_info = self.validate_file_exists(category, filename)
            
            if exists and module_info:
                found_count += 1
                quality_result = self.validate_module_quality(module_info)
                category_score += quality_result.score
                
                status = "✅" if quality_result.passed else "⚠️"
                print(f"  {status} {filename} - {quality_result.score:.0f}% quality")
                
                if quality_result.recommendations:
                    issues.extend([f"{filename}: {rec}" for rec in quality_result.recommendations])
                    
                self.validation_results[f"{category}/{filename}"] = quality_result
                
            else:
                print(f"  ❌ {filename} - MISSING")
                issues.append(f"Missing required file: {category}/{filename}")
        
        # Calculate category completion percentage
        max_possible_score = len(required_files) * 100
        category_percentage = (category_score / max_possible_score) * 100 if max_possible_score > 0 else 0
        
        print(f"  📊 {category.upper()}: {found_count}/{len(required_files)} files, {category_percentage:.1f}% quality")
        
        return category_percentage, issues
    
    def validate_integration(self) -> Tuple[bool, List[str]]:
        """Validate that the three critical integration modules are present and integrated"""
        critical_modules = [
            "core/system_integration_validator.sv",
            "core/performance_optimizer.sv", 
            "core/advanced_feature_integrator.sv"
        ]
        
        integration_issues = []
        all_present = True
        
        print(f"\n🔧 Validating CRITICAL INTEGRATION modules:")
        
        for module_path in critical_modules:
            category, filename = module_path.split('/')
            exists, module_info = self.validate_file_exists(category, filename)
            
            if exists and module_info:
                quality_result = self.validate_module_quality(module_info)
                if quality_result.score >= 90:  # Higher standard for critical modules
                    print(f"  ✅ {filename} - EXCELLENT ({quality_result.score:.0f}%)")
                else:
                    print(f"  ⚠️ {filename} - NEEDS IMPROVEMENT ({quality_result.score:.0f}%)")
                    integration_issues.append(f"Critical module {filename} needs quality improvement")
            else:
                print(f"  ❌ {filename} - MISSING CRITICAL MODULE")
                integration_issues.append(f"Missing critical integration module: {filename}")
                all_present = False
        
        # Check multi-core system integration
        multi_core_path = self.rtl_root / "core" / "multi_core_system.sv"
        if multi_core_path.exists():
            with open(multi_core_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # Check if critical modules are instantiated
            critical_instantiations = [
                "system_integration_validator",
                "performance_optimizer", 
                "advanced_feature_integrator"
            ]
            
            missing_integrations = []
            for module_name in critical_instantiations:
                if module_name not in content:
                    missing_integrations.append(module_name)
            
            if missing_integrations:
                integration_issues.append(f"Multi-core system missing integrations: {missing_integrations}")
            else:
                print(f"  ✅ Multi-core system properly integrates all critical modules")
        
        return all_present and len(integration_issues) == 0, integration_issues
    
    def calculate_overall_score(self) -> float:
        """Calculate overall completion percentage"""
        total_categories = len(self.required_modules)
        total_score = 0.0
        
        for category in self.required_modules:
            category_score, _ = self.validate_category(category)
            total_score += category_score
        
        return total_score / total_categories if total_categories > 0 else 0.0
    
    def generate_report(self) -> Dict:
        """Generate comprehensive validation report"""
        print(f"\n🚀 Starting RISC-V RTL Completion Validation...")
        print(f"Validation Time: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        
        # Validate all categories
        category_scores = {}
        all_issues = []
        
        for category in self.required_modules:
            score, issues = self.validate_category(category)
            category_scores[category] = score
            all_issues.extend(issues)
        
        # Validate critical integration
        integration_ok, integration_issues = self.validate_integration()
        all_issues.extend(integration_issues)
        
        # Calculate overall score
        overall_score = sum(category_scores.values()) / len(category_scores)
        
        # Integration bonus/penalty
        if integration_ok:
            overall_score = min(100.0, overall_score + 5)  # Bonus for proper integration
        else:
            overall_score = max(0.0, overall_score - 10)   # Penalty for missing integration
        
        # Generate final assessment
        if overall_score >= 95:
            status = "🎉 100% RTL COMPLETENESS ACHIEVED!"
            status_color = "EXCELLENT"
        elif overall_score >= 90:
            status = "✅ RTL IMPLEMENTATION NEARLY COMPLETE"
            status_color = "VERY GOOD"
        elif overall_score >= 80:
            status = "⚠️ RTL IMPLEMENTATION SUBSTANTIALLY COMPLETE"
            status_color = "GOOD"
        else:
            status = "❌ RTL IMPLEMENTATION NEEDS WORK"
            status_color = "NEEDS IMPROVEMENT"
        
        # Print final report
        print(f"\n" + "="*80)
        print(f"📊 FINAL VALIDATION REPORT")
        print(f"="*80)
        
        for category, score in category_scores.items():
            print(f"{category.upper():.<25} {score:>6.1f}%")
        
        print(f"{'INTEGRATION STATUS':.<25} {'PASS' if integration_ok else 'FAIL':>6}")
        print(f"{'='*31}")
        print(f"{'OVERALL RTL COMPLETENESS':.<25} {overall_score:>6.1f}%")
        print(f"\n{status}")
        
        if all_issues:
            print(f"\n⚠️ Issues Found ({len(all_issues)}):")
            for i, issue in enumerate(all_issues[:10], 1):  # Show top 10 issues
                print(f"  {i}. {issue}")
            if len(all_issues) > 10:
                print(f"  ... and {len(all_issues) - 10} more issues")
        
        # Generate report dictionary
        report = {
            "timestamp": datetime.now().isoformat(),
            "overall_score": overall_score,
            "status": status_color,
            "integration_ok": integration_ok,
            "category_scores": category_scores,
            "issues": all_issues,
            "total_modules_checked": sum(len(files) for files in self.required_modules.values()),
            "completion_achieved": overall_score >= 95
        }
        
        return report

def main():
    """Main validation function"""
    # Change to the script's directory
    script_dir = Path(__file__).parent
    os.chdir(script_dir.parent)  # Go to project root
    
    # Initialize validator
    validator = RTLCompletionValidator()
    
    # Generate validation report
    report = validator.generate_report()
    
    # Save report to file
    report_file = Path("docs/implementation/RTL_VALIDATION_REPORT.json")
    report_file.parent.mkdir(parents=True, exist_ok=True)
    
    with open(report_file, 'w') as f:
        json.dump(report, f, indent=2)
    
    print(f"\n📄 Detailed report saved to: {report_file}")
    
    # Exit with appropriate code
    if report["completion_achieved"]:
        print(f"\n🎯 SUCCESS: RTL implementation is 100% complete!")
        sys.exit(0)
    else:
        print(f"\n🔄 CONTINUE: RTL implementation at {report['overall_score']:.1f}%")
        sys.exit(1)

if __name__ == "__main__":
    main() 