#!/bin/bash
#=============================================================================
# RISC-V Cache Architecture CI/CD Validation Script
# 
# This script runs comprehensive cache architecture validation tests
# and is designed to be used in any CI/CD pipeline (Jenkins, GitLab CI, etc.)
#
# Usage:
#   ./scripts/ci_cache_validation.sh [--quick] [--report-dir=DIR]
#
# Exit Codes:
#   0: All validations passed
#   1: Critical validation failures
#   2: Warning-level issues (configurable)
#=============================================================================

set -euo pipefail  # Exit on error, undefined vars, pipe failures

# Script configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
REPORT_DIR="${PROJECT_ROOT}/validation_reports"
QUICK_MODE=false
VERBOSE=false
EXIT_ON_WARNING=false

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Logging functions
log_info() {
    echo -e "${GREEN}✅ [INFO]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}⚠️  [WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}❌ [ERROR]${NC} $1"
}

log_debug() {
    if [[ "$VERBOSE" == "true" ]]; then
        echo -e "${BLUE}🔍 [DEBUG]${NC} $1"
    fi
}

# Parse command line arguments
parse_args() {
    while [[ $# -gt 0 ]]; do
        case $1 in
            --quick)
                QUICK_MODE=true
                log_info "Quick mode enabled - running basic tests only"
                shift
                ;;
            --report-dir=*)
                REPORT_DIR="${1#*=}"
                log_info "Report directory set to: $REPORT_DIR"
                shift
                ;;
            --verbose|-v)
                VERBOSE=true
                log_info "Verbose mode enabled"
                shift
                ;;
            --exit-on-warning)
                EXIT_ON_WARNING=true
                log_info "Will exit on warnings"
                shift
                ;;
            --help|-h)
                show_help
                exit 0
                ;;
            *)
                log_error "Unknown option: $1"
                show_help
                exit 1
                ;;
        esac
    done
}

show_help() {
    cat << EOF
RISC-V Cache Architecture CI/CD Validation Script

Usage: $0 [OPTIONS]

Options:
    --quick                 Run only basic/fast validation tests
    --report-dir=DIR        Directory to save validation reports (default: validation_reports)
    --verbose, -v           Enable verbose output
    --exit-on-warning       Exit with code 2 on warnings (strict mode)
    --help, -h              Show this help message

Examples:
    $0                      # Run full validation suite
    $0 --quick              # Run basic tests only (faster)
    $0 --verbose --report-dir=/tmp/reports
    
Exit Codes:
    0: All validations passed
    1: Critical validation failures
    2: Warning-level issues (when --exit-on-warning is used)
EOF
}

# Environment setup
setup_environment() {
    log_info "🚀 Starting Cache Architecture CI/CD Validation"
    log_info "Project Root: $PROJECT_ROOT"
    log_info "Report Directory: $REPORT_DIR"
    log_info "Timestamp: $(date '+%Y-%m-%d %H:%M:%S')"
    
    # Create report directory
    mkdir -p "$REPORT_DIR"
    
    # Check Python availability
    if ! command -v python3 &> /dev/null; then
        log_error "Python 3 is required but not installed"
        exit 1
    fi
    
    # Check if validation scripts exist
    local required_scripts=(
        "$SCRIPT_DIR/validate_cache_architecture.py"
        "$SCRIPT_DIR/test_parameter_scenarios.py"
    )
    
    for script in "${required_scripts[@]}"; do
        if [[ ! -f "$script" ]]; then
            log_error "Required validation script not found: $script"
            exit 1
        fi
    done
    
    log_info "✅ Environment setup complete"
}

# Run cache architecture validation
run_architecture_validation() {
    log_info "🔍 Running Cache Architecture Validation..."
    
    local report_file="$REPORT_DIR/cache_architecture_validation.json"
    local verbose_flag=""
    
    if [[ "$VERBOSE" == "true" ]]; then
        verbose_flag="--verbose"
    fi
    
    if python3 "$SCRIPT_DIR/validate_cache_architecture.py" \
        --project-root="$PROJECT_ROOT" \
        $verbose_flag \
        --report="$report_file"; then
        log_info "✅ Cache architecture validation PASSED"
        return 0
    else
        log_error "❌ Cache architecture validation FAILED"
        return 1
    fi
}

# Run parameter scenario tests  
run_parameter_tests() {
    log_info "🧪 Running Parameter Scenario Tests..."
    
    local test_type="basic"
    if [[ "$QUICK_MODE" == "false" ]]; then
        test_type="full"
    fi
    
    local report_file="$REPORT_DIR/parameter_scenarios_${test_type}.json"
    local verbose_flag=""
    
    if [[ "$VERBOSE" == "true" ]]; then
        verbose_flag="--verbose"
    fi
    
    if python3 "$SCRIPT_DIR/test_parameter_scenarios.py" \
        --project-root="$PROJECT_ROOT" \
        --scenarios="$test_type" \
        $verbose_flag \
        --report="$report_file"; then
        log_info "✅ Parameter scenario tests PASSED"
        return 0
    else
        log_error "❌ Parameter scenario tests FAILED"
        return 1
    fi
}

# Run basic syntax checks (if tools available)
run_syntax_checks() {
    log_info "📝 Running Basic Syntax Checks..."
    
    # Check for SystemVerilog syntax with available tools
    local syntax_errors=0
    
    # Try verilator if available
    if command -v verilator &> /dev/null; then
        log_debug "Using Verilator for syntax checking"
        
        local key_files=(
            "$PROJECT_ROOT/rtl/pkg/riscv_cache_topology_pkg.sv"
            "$PROJECT_ROOT/rtl/memory/cache_cluster_manager.sv"
            "$PROJECT_ROOT/rtl/core/multi_core_system.sv"
        )
        
        for file in "${key_files[@]}"; do
            if [[ -f "$file" ]]; then
                log_debug "Checking syntax: $(basename "$file")"
                if ! verilator --lint-only "$file" 2>/dev/null; then
                    log_warn "Syntax issues detected in $(basename "$file")"
                    syntax_errors=$((syntax_errors + 1))
                fi
            fi
        done
    else
        log_debug "Verilator not available, skipping syntax checks"
    fi
    
    if [[ $syntax_errors -eq 0 ]]; then
        log_info "✅ Basic syntax checks PASSED"
        return 0
    else
        log_warn "⚠️ $syntax_errors syntax issues detected"
        return 2  # Warning level
    fi
}

# Generate summary report
generate_summary() {
    local arch_result=$1
    local param_result=$2
    local syntax_result=$3
    
    local summary_file="$REPORT_DIR/validation_summary.txt"
    
    cat > "$summary_file" << EOF
=============================================================================
RISC-V Cache Architecture CI/CD Validation Summary
=============================================================================
Timestamp: $(date '+%Y-%m-%d %H:%M:%S')
Project Root: $PROJECT_ROOT
Test Mode: $([ "$QUICK_MODE" == "true" ] && echo "Quick" || echo "Full")

Test Results:
-------------
Cache Architecture Validation: $([ $arch_result -eq 0 ] && echo "✅ PASSED" || echo "❌ FAILED")
Parameter Scenario Tests:      $([ $param_result -eq 0 ] && echo "✅ PASSED" || echo "❌ FAILED")
Basic Syntax Checks:           $([ $syntax_result -eq 0 ] && echo "✅ PASSED" || [ $syntax_result -eq 2 ] && echo "⚠️ WARNINGS" || echo "❌ FAILED")

Overall Status: $([ $arch_result -eq 0 ] && [ $param_result -eq 0 ] && echo "✅ PASSED" || echo "❌ FAILED")

Reports Location: $REPORT_DIR
=============================================================================
EOF
    
    # Display summary
    cat "$summary_file"
    
    log_info "📄 Summary report saved to: $summary_file"
}

# Main execution
main() {
    # Parse arguments
    parse_args "$@"
    
    # Setup environment
    setup_environment
    
    # Initialize result tracking
    local arch_validation_result=0
    local parameter_test_result=0
    local syntax_check_result=0
    local overall_result=0
    
    # Run validations
    echo "
=============================================================================
RUNNING VALIDATION TESTS
============================================================================="
    
    # 1. Cache Architecture Validation
    if ! run_architecture_validation; then
        arch_validation_result=1
        overall_result=1
    fi
    
    echo ""
    
    # 2. Parameter Scenario Tests
    if ! run_parameter_tests; then
        parameter_test_result=1
        overall_result=1
    fi
    
    echo ""
    
    # 3. Basic Syntax Checks (optional)
    run_syntax_checks
    syntax_check_result=$?
    
    # Handle warnings
    if [[ $syntax_check_result -eq 2 ]] && [[ "$EXIT_ON_WARNING" == "true" ]]; then
        overall_result=2
    fi
    
    echo "
=============================================================================
VALIDATION SUMMARY
============================================================================="
    
    # Generate and display summary
    generate_summary $arch_validation_result $parameter_test_result $syntax_check_result
    
    # Final status
    if [[ $overall_result -eq 0 ]]; then
        log_info "🎉 ALL CACHE ARCHITECTURE VALIDATIONS PASSED!"
        log_info "✅ Cache system is ready for deployment"
    elif [[ $overall_result -eq 2 ]]; then
        log_warn "⚠️ VALIDATION COMPLETED WITH WARNINGS"
        log_warn "Cache system has minor issues that may need attention"
    else
        log_error "❌ CACHE ARCHITECTURE VALIDATION FAILED"
        log_error "Critical issues detected - deployment not recommended"
    fi
    
    exit $overall_result
}

# Run main function with all arguments
main "$@" 