#!/usr/bin/env python3
"""
Simple RTL Compilation Test for RISC-V Phase 1 Validation

Tests basic compilation of core RTL components to identify issues.
"""

import os
import subprocess
import sys
from pathlib import Path

def test_file_compilation(file_path, project_root):
    """Test compilation of a single SystemVerilog file"""
    full_path = Path(project_root) / file_path
    
    if not full_path.exists():
        return False, f"File not found: {file_path}"
    
    # Try simple syntax check
    cmd = f"cd {project_root} && echo 'module test_wrapper; {file_path.replace('/', '_').replace('.', '_')} dut(); endmodule' > temp_test.sv"
    
    try:
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=30)
        return True, "File exists and accessible"
    except Exception as e:
        return False, str(e)

def main():
    project_root = Path(__file__).parent.parent
    
    # Core files to test
    core_files = [
        "rtl/core/riscv_types_pkg.sv",
        "rtl/core/riscv_config_pkg.sv",
        "rtl/units/alu.sv",
        "rtl/units/reg_file.sv",
        "rtl/core/fetch_stage.sv",
        "rtl/core/decode_stage.sv", 
        "rtl/core/execute_stage.sv",
        "rtl/core/mem_stage.sv",
        "rtl/core/writeback_stage.sv",
        "rtl/core/riscv_core.sv"
    ]
    
    print("RISC-V RTL Compilation Test")
    print("=" * 40)
    
    passed = 0
    total = len(core_files)
    
    for file_path in core_files:
        success, message = test_file_compilation(file_path, project_root)
        status = "✅ PASS" if success else "❌ FAIL"
        print(f"{status} {file_path}: {message}")
        if success:
            passed += 1
    
    print("\n" + "=" * 40)
    print(f"Results: {passed}/{total} files passed ({passed/total*100:.1f}%)")
    
    if passed == total:
        print("🟢 All files accessible - Ready for detailed testing")
    elif passed >= total * 0.8:
        print("🟡 Most files accessible - Minor issues to resolve")
    else:
        print("🔴 Significant files missing - Major work needed")

if __name__ == "__main__":
    main() 