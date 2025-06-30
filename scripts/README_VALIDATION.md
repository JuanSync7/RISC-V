# Cache Architecture Validation Scripts

This directory contains comprehensive validation scripts for the RISC-V cache architecture, designed to ensure system integrity and catch regressions in CI/CD pipelines.

## 📋 Overview

The validation suite consists of three main components:

1. **`validate_cache_architecture.py`** - Core architecture integrity validation
2. **`test_parameter_scenarios.py`** - Parameter adaptation scenario testing  
3. **`ci_cache_validation.sh`** - Universal CI/CD orchestration script

## 🚀 Quick Start

### Basic Validation
```bash
# Run basic validation (fast)
python scripts/validate_cache_architecture.py

# Run parameter scenario tests
python scripts/test_parameter_scenarios.py --scenarios=basic

# Run complete CI/CD validation
./scripts/ci_cache_validation.sh --quick
```

### Comprehensive Validation
```bash
# Run full architecture validation with reports
python scripts/validate_cache_architecture.py --verbose --report=cache_report.json

# Run comprehensive parameter testing
python scripts/test_parameter_scenarios.py --scenarios=full --verbose

# Run complete validation suite
./scripts/ci_cache_validation.sh --verbose
```

## 📖 Detailed Documentation

### 1. Cache Architecture Validator (`validate_cache_architecture.py`)

**Purpose:** Validates the structural integrity and integration of the cache topology system.

**What it checks:**
- ✅ File structure and presence of all required components
- ✅ Cache topology package completeness (enums, functions, validation)
- ✅ Cache cluster manager implementation (multi-instance support)
- ✅ Multi-core system integration (topology selection logic)
- ✅ Configuration parameters (topology, instances, controllers)
- ✅ Package import structure and dependencies

**Usage:**
```bash
# Basic validation
python scripts/validate_cache_architecture.py

# Verbose mode with report generation
python scripts/validate_cache_architecture.py --verbose --report=validation.json

# Custom project root
python scripts/validate_cache_architecture.py --project-root=/path/to/project

# Strict mode (exit on warnings)
python scripts/validate_cache_architecture.py --exit-on-warning
```

**Exit Codes:**
- `0`: All validations passed
- `1`: Critical validation failures detected
- `2`: Warning-level issues detected (when `--exit-on-warning` used)

### 2. Parameter Scenario Tester (`test_parameter_scenarios.py`)

**Purpose:** Tests that the cache system correctly adapts to different parameter configurations.

**What it tests:**
- ✅ Core count adaptation (1-12+ cores)
- ✅ Topology selection logic (UNIFIED → CLUSTERED → NUMA)
- ✅ Cache instance scaling (L2/L3 counts)
- ✅ Memory controller adaptation
- ✅ Cache size parameter handling

**Test Scenarios:**

| Scenario | Cores | Topology | L2 Instances | L3 Instances |
|----------|-------|----------|--------------|--------------|
| Single Core | 1 | UNIFIED | 1 | 1 |
| Dual Core | 2 | UNIFIED | 1 | 1 |
| Quad Core | 4 | CLUSTERED | 2 | 1 |
| Octa Core | 8 | NUMA | 2 | 2 |
| Large System | 12 | NUMA | 3 | 3 |

**Usage:**
```bash
# Quick basic scenarios (CI/CD friendly)
python scripts/test_parameter_scenarios.py --scenarios=basic

# Comprehensive testing
python scripts/test_parameter_scenarios.py --scenarios=full --verbose

# With report generation
python scripts/test_parameter_scenarios.py --report=param_test.json
```

### 3. CI/CD Orchestration Script (`ci_cache_validation.sh`)

**Purpose:** Universal shell script for any CI/CD system (Jenkins, GitLab CI, etc.)

**Features:**
- 🔧 **Universal compatibility** - Works with any CI/CD system
- ⚡ **Quick mode** - Fast validation for frequent checks
- 📊 **Report generation** - JSON and text reports
- 🎨 **Colored output** - Easy-to-read results
- 🔍 **Syntax checking** - Optional SystemVerilog validation

**Usage:**
```bash
# Quick validation (basic tests only)
./scripts/ci_cache_validation.sh --quick

# Full validation with verbose output
./scripts/ci_cache_validation.sh --verbose

# Custom report directory
./scripts/ci_cache_validation.sh --report-dir=/tmp/cache_reports

# Strict mode (fail on warnings)
./scripts/ci_cache_validation.sh --exit-on-warning
```

## 🔄 CI/CD Integration

### GitHub Actions

The provided `.github/workflows/cache_validation.yml` demonstrates integration:

```yaml
# Runs on every push to core/memory RTL files
on:
  push:
    paths:
      - 'rtl/core/**'
      - 'rtl/memory/**'
      - 'scripts/**'
  pull_request:
    branches: [ main ]
```

**Features:**
- ✅ Matrix testing (basic + full scenarios)
- ✅ Automatic PR comments with results
- ✅ Report artifact upload
- ✅ Nightly scheduled runs

### Jenkins Integration

```groovy
pipeline {
    agent any
    stages {
        stage('Cache Validation') {
            steps {
                sh './scripts/ci_cache_validation.sh --verbose --report-dir=reports'
            }
            post {
                always {
                    archiveArtifacts artifacts: 'reports/**', fingerprint: true
                    publishHTML([
                        allowMissing: false,
                        alwaysLinkToLastBuild: true,
                        keepAll: true,
                        reportDir: 'reports',
                        reportFiles: 'validation_summary.txt',
                        reportName: 'Cache Validation Report'
                    ])
                }
            }
        }
    }
}
```

### GitLab CI Integration

```yaml
cache_validation:
  stage: test
  script:
    - ./scripts/ci_cache_validation.sh --quick --report-dir=reports
  artifacts:
    reports:
      junit: reports/*.json
    paths:
      - reports/
    expire_in: 1 week
  only:
    changes:
      - rtl/core/**/*
      - rtl/memory/**/*
      - scripts/**/*
```

## 📊 Reports and Outputs

### JSON Reports

Both Python scripts generate detailed JSON reports:

```json
{
  "timestamp": "2024-01-27T10:30:00",
  "validation_results": {
    "File Structure": "PASS",
    "Topology Package": "PASS",
    "Cluster Manager": "PASS"
  },
  "summary": {
    "total_validations": 7,
    "passed_validations": 7,
    "failed_validations": 0,
    "error_count": 0,
    "warning_count": 0
  },
  "errors": [],
  "warnings": []
}
```

### Text Summary

The shell script generates human-readable summaries:

```
=============================================================================
RISC-V Cache Architecture CI/CD Validation Summary
=============================================================================
Timestamp: 2024-01-27 10:30:00
Project Root: /path/to/project
Test Mode: Full

Test Results:
-------------
Cache Architecture Validation: ✅ PASSED
Parameter Scenario Tests:      ✅ PASSED
Basic Syntax Checks:           ✅ PASSED

Overall Status: ✅ PASSED
=============================================================================
```

## 🎯 Best Practices for CI/CD

### 1. **Layered Testing Strategy**

```bash
# Stage 1: Quick validation (every commit)
./scripts/ci_cache_validation.sh --quick

# Stage 2: Full validation (pull requests)
./scripts/ci_cache_validation.sh

# Stage 3: Comprehensive testing (nightly)
./scripts/ci_cache_validation.sh --verbose --scenarios=full
```

### 2. **Failure Handling**

```bash
# Run validation and handle different exit codes
if ./scripts/ci_cache_validation.sh; then
    echo "✅ Cache validation passed"
elif [ $? -eq 2 ]; then
    echo "⚠️ Cache validation passed with warnings"
    # Optionally allow warnings in non-production branches
else
    echo "❌ Cache validation failed"
    exit 1
fi
```

### 3. **Report Archival**

Always archive validation reports for debugging and historical analysis:

```bash
# Generate timestamped reports
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
./scripts/ci_cache_validation.sh --report-dir="reports/${TIMESTAMP}"

# Archive for later analysis
tar -czf "cache_validation_${TIMESTAMP}.tar.gz" "reports/${TIMESTAMP}"
```

## 🔧 Customization

### Adding New Validation Checks

To add custom validation checks, extend the `CacheArchitectureValidator` class:

```python
def validate_custom_feature(self) -> bool:
    """Custom validation logic"""
    # Your validation code here
    return True

# Add to validations list in run_comprehensive_validation()
validations = [
    # ... existing validations ...
    ("Custom Feature", self.validate_custom_feature)
]
```

### Adding New Parameter Scenarios

Extend the scenario lists in `test_parameter_scenarios.py`:

```python
def get_custom_scenarios(self) -> List[Dict]:
    return [
        {
            "name": "Custom Scenario",
            "cores": 16,
            "expected_topology": "NUMA",
            "expected_l2": 4,
            "expected_l3": 4,
            "cache_size_kb": 2048
        }
    ]
```

## ⚠️ Troubleshooting

### Common Issues

1. **Python not found**
   ```bash
   # Ensure Python 3 is installed and in PATH
   which python3
   python3 --version
   ```

2. **Permission denied on shell script**
   ```bash
   chmod +x scripts/ci_cache_validation.sh
   ```

3. **Missing validation scripts**
   ```bash
   # Verify scripts exist
   ls -la scripts/validate_cache_architecture.py
   ls -la scripts/test_parameter_scenarios.py
   ```

4. **SystemVerilog syntax errors**
   ```bash
   # Install Verilator for syntax checking
   sudo apt-get install verilator
   ```

## 📞 Support

For issues with the validation scripts:

1. Check this documentation first
2. Review the verbose output: `--verbose` flag
3. Examine generated reports in JSON format
4. Verify all required files are present
5. Test scripts manually outside CI/CD environment

## 🎉 Summary

These validation scripts provide comprehensive coverage of the cache architecture system:

- **✅ Structural integrity** - All components present and integrated
- **✅ Parameter adaptation** - System responds correctly to configuration changes  
- **✅ Scalability validation** - Multi-core scenarios work as expected
- **✅ CI/CD ready** - Proper exit codes, reports, and automation support

The scripts are designed to catch regressions early and ensure the cache system maintains its enterprise-grade quality as development continues. 