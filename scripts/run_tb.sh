#!/usr/bin/env bash
# ============================================================================
# Script: run_tb.sh
# Purpose: Compile and run a SystemVerilog testbench using Icarus Verilog.
# Usage:   ./run_tb.sh <testbench_file.sv> [waveform]
#          If "waveform" is specified, a VCD file will be generated.
# ----------------------------------------------------------------------------
# Requirements:
#   - Icarus Verilog (iverilog + vvp)
#   - VPI support for SystemVerilog (by using -g2012 flag)
# ----------------------------------------------------------------------------
# Example:
#   ./run_tb.sh tb/atomic_unit_tb.sv waveform
# ============================================================================

set -e

if [ "$#" -lt 1 ]; then
  echo "Usage: $0 <testbench_file.sv> [waveform]" >&2
  exit 1
fi

TB_FILE=$1
shift

WAVEFORM=0
if [ "$1" == "waveform" ]; then
  WAVEFORM=1
fi

# Output file names
TOP_MODULE=$(basename "$TB_FILE" .sv)
OUTPUT="build/${TOP_MODULE}.out"
VCD_FILE="${TOP_MODULE}.vcd"

mkdir -p build

# Compile
iverilog -g2012 -Wall -I rtl -I rtl/interfaces -I tb -o "$OUTPUT" "$TB_FILE"

# Run
if [ $WAVEFORM -eq 1 ]; then
  vvp "$OUTPUT" +dump_vcd
  echo "Waveform generated: ${VCD_FILE}"
else
  vvp "$OUTPUT"
fi