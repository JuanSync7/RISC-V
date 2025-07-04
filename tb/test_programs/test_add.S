# test_add.S - Test ADD and ADDI instructions
# RISC-V RV32I Assembly Test Program
#
# This test verifies basic ALU ADD operations
# Expected result: x10 = 111 (decimal)

.section .text
.globl _start

_start:
    # Initialize registers
    li      x1, 0           # x1 = 0
    li      x2, 0           # x2 = 0
    
    # Test ADDI (add immediate)
    addi    x1, x0, 10      # x1 = 0 + 10 = 10
    addi    x2, x1, 20      # x2 = 10 + 20 = 30
    addi    x3, x2, -5      # x3 = 30 + (-5) = 25
    
    # Test ADD (register-register)
    add     x4, x1, x2      # x4 = 10 + 30 = 40
    add     x5, x3, x4      # x5 = 25 + 40 = 65
    add     x6, x5, x1      # x6 = 65 + 10 = 75
    
    # Test with negative numbers
    li      x7, -10         # x7 = -10
    add     x8, x6, x7      # x8 = 75 + (-10) = 65
    
    # Chain of additions
    addi    x9, x0, 1       # x9 = 1
    add     x9, x9, x9      # x9 = 1 + 1 = 2
    add     x9, x9, x9      # x9 = 2 + 2 = 4
    add     x9, x9, x9      # x9 = 4 + 4 = 8
    add     x9, x9, x9      # x9 = 8 + 8 = 16
    
    # Final calculation
    add     x10, x8, x9     # x10 = 65 + 16 = 81
    addi    x10, x10, 30    # x10 = 81 + 30 = 111
    
    # Store result to test pass marker
    li      x11, 0x10000000 # Test pass address
    sw      x10, 0(x11)     # Store result (triggers test pass)
    
    # Infinite loop (should never reach here)
done:
    j       done

# Test data section
.section .data
test_name:
    .string "ADD_TEST"
expected_result:
    .word   111

# Build instructions:
# riscv32-unknown-elf-as -o test_add.o test_add.S
# riscv32-unknown-elf-ld -Ttext=0x0 -o test_add.elf test_add.o
# riscv32-unknown-elf-objcopy -O binary test_add.elf test_add.bin
# xxd -g 1 -c 4 test_add.bin | awk '{print $5$4$3$2}' > test_add.hex