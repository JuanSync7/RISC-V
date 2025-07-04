#!/bin/bash
#=============================================================================
# build_with_profile.sh - Build RISC-V core with different configuration profiles
#
# Usage: ./build_with_profile.sh [profile] [simulator]
#   profile: small, medium, large, custom (default: medium)
#   simulator: vcs, modelsim, xcelium, verilator (default: vcs)
#
# Example:
#   ./build_with_profile.sh small modelsim
#=============================================================================

# Set defaults
PROFILE=${1:-medium}
SIMULATOR=${2:-vcs}
BUILD_DIR="build_${PROFILE}_${SIMULATOR}"

# Color codes for output
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

echo -e "${GREEN}==================================================================${NC}"
echo -e "${GREEN}Building RISC-V Core with Profile: ${YELLOW}${PROFILE}${NC}"
echo -e "${GREEN}Using Simulator: ${YELLOW}${SIMULATOR}${NC}"
echo -e "${GREEN}==================================================================${NC}"

# Create build directory
mkdir -p ${BUILD_DIR}
cd ${BUILD_DIR}

# Set profile define
case ${PROFILE} in
    small)
        PROFILE_DEFINE="+define+PROFILE_SMALL"
        echo -e "${YELLOW}Using Small Profile: 8KB caches, simple policies, FPGA-optimized${NC}"
        ;;
    large)
        PROFILE_DEFINE="+define+PROFILE_LARGE"
        echo -e "${YELLOW}Using Large Profile: 64KB+ caches, advanced features, ASIC-optimized${NC}"
        ;;
    custom)
        PROFILE_DEFINE="+define+PROFILE_CUSTOM"
        echo -e "${YELLOW}Using Custom Profile: User-defined configuration${NC}"
        ;;
    medium|*)
        PROFILE_DEFINE=""  # Default profile
        echo -e "${YELLOW}Using Medium Profile: 32KB caches, balanced configuration${NC}"
        ;;
esac

# Common compile flags
COMMON_FLAGS="-sverilog -timescale=1ns/1ps +define+SIMULATION"

# Build file list in dependency order
RTL_FILES=(
    # Base packages (must be first)
    "../rtl/packages/base/riscv_base_pkg.sv"
    
    # Domain packages
    "../rtl/packages/domain/riscv_cache_config_pkg.sv"
    "../rtl/packages/domain/riscv_core_config_pkg.sv"
    "../rtl/packages/domain/riscv_memory_config_pkg.sv"
    "../rtl/packages/domain/riscv_ooo_config_pkg.sv"
    
    # Profile packages
    "../rtl/packages/profiles/riscv_profile_small.sv"
    "../rtl/packages/profiles/riscv_profile_medium.sv"
    "../rtl/packages/profiles/riscv_profile_large.sv"
    "../rtl/packages/profiles/riscv_profile_custom.sv"
    
    # System config (uses selected profile)
    "../rtl/packages/riscv_system_config_pkg.sv"
    
    # Existing packages that need updating
    "../rtl/shared/packages/*.sv"
    "../rtl/shared/interfaces/*.sv"
    
    # Core RTL files
    "../rtl/units/*.sv"
    "../rtl/memory/*.sv"
    "../rtl/core/pipeline/*.sv"
    "../rtl/core/control/*.sv"
    "../rtl/core/*.sv"
)

# Simulator-specific compilation
case ${SIMULATOR} in
    vcs)
        echo -e "\n${GREEN}Compiling with VCS...${NC}"
        vcs ${COMMON_FLAGS} ${PROFILE_DEFINE} \
            +lint=TFIPC-L +warn=all \
            -debug_access+all -kdb -lca \
            +incdir+../rtl/packages \
            +incdir+../rtl/shared/packages \
            +incdir+../rtl/core \
            "${RTL_FILES[@]}" \
            -top riscv_core \
            -o simv_${PROFILE}
        ;;
        
    modelsim)
        echo -e "\n${GREEN}Compiling with ModelSim...${NC}"
        vlog ${COMMON_FLAGS} ${PROFILE_DEFINE} \
            +incdir+../rtl/packages \
            +incdir+../rtl/shared/packages \
            +incdir+../rtl/core \
            "${RTL_FILES[@]}"
        ;;
        
    xcelium)
        echo -e "\n${GREEN}Compiling with Xcelium...${NC}"
        xmvlog ${COMMON_FLAGS} ${PROFILE_DEFINE} \
            +incdir+../rtl/packages \
            +incdir+../rtl/shared/packages \
            +incdir+../rtl/core \
            "${RTL_FILES[@]}"
        ;;
        
    verilator)
        echo -e "\n${GREEN}Compiling with Verilator...${NC}"
        verilator --sv ${PROFILE_DEFINE} \
            --timescale 1ns/1ps \
            -I../rtl/packages \
            -I../rtl/shared/packages \
            -I../rtl/core \
            --lint-only \
            --top-module riscv_core \
            "${RTL_FILES[@]}"
        ;;
        
    *)
        echo -e "${RED}Error: Unknown simulator ${SIMULATOR}${NC}"
        exit 1
        ;;
esac

# Check compilation status
if [ $? -eq 0 ]; then
    echo -e "\n${GREEN}==================================================================${NC}"
    echo -e "${GREEN}Build completed successfully!${NC}"
    echo -e "${GREEN}Profile: ${YELLOW}${PROFILE}${GREEN}, Simulator: ${YELLOW}${SIMULATOR}${NC}"
    echo -e "${GREEN}Build directory: ${YELLOW}${BUILD_DIR}${NC}"
    
    # Show configuration summary
    echo -e "\n${GREEN}Configuration Summary:${NC}"
    case ${PROFILE} in
        small)
            echo "  - Single core, in-order execution"
            echo "  - 8KB L1 caches, no L2/L3"
            echo "  - Simple branch predictor"
            echo "  - Target: 50MHz FPGA"
            ;;
        large)
            echo "  - 4 cores, out-of-order execution"
            echo "  - 64KB L1, 512KB L2, 8MB L3 caches"
            echo "  - Tournament branch predictor"
            echo "  - Target: 1GHz ASIC"
            ;;
        medium|*)
            echo "  - 2 cores, in-order execution"
            echo "  - 32KB L1, 256KB L2 caches"
            echo "  - Standard branch predictor"
            echo "  - Target: 200MHz FPGA/ASIC"
            ;;
    esac
    echo -e "${GREEN}==================================================================${NC}"
else
    echo -e "\n${RED}==================================================================${NC}"
    echo -e "${RED}Build failed! Check error messages above.${NC}"
    echo -e "${RED}==================================================================${NC}"
    exit 1
fi

# Generate configuration report
echo -e "\n${GREEN}Generating configuration report...${NC}"
cat > config_report_${PROFILE}.txt << EOF
RISC-V Core Configuration Report
================================
Profile: ${PROFILE}
Date: $(date)
Simulator: ${SIMULATOR}

Configuration Details:
$(grep -E "(CONFIG_|DEFAULT_)" ../rtl/packages/profiles/riscv_profile_${PROFILE}.sv 2>/dev/null | head -20)

Build Command:
${0} ${@}

Build Directory: ${BUILD_DIR}
EOF

echo -e "${GREEN}Configuration report saved to: ${YELLOW}config_report_${PROFILE}.txt${NC}"

# Optional: Run quick test
echo -e "\n${YELLOW}To run a quick test:${NC}"
case ${SIMULATOR} in
    vcs)
        echo "  cd ${BUILD_DIR} && ./simv_${PROFILE} +TEST=sanity"
        ;;
    modelsim)
        echo "  cd ${BUILD_DIR} && vsim -c -do \"run -all; quit\" tb_top"
        ;;
    *)
        echo "  Check your simulator documentation for run commands"
        ;;
esac

exit 0