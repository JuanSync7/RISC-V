# RISC-V Compressed (RVC) Instruction Decoding

## 1. Overview
RISC-V Compressed (RVC) instructions are 16-bit instructions that provide a denser instruction encoding for common operations, reducing code size and improving instruction fetch bandwidth. This document outlines the architectural considerations and implementation plan for supporting RVC instructions.

## 2. RVC Instruction Format
RVC instructions are 16 bits long, unlike the standard 32-bit RISC-V instructions. They are identified by their two least significant bits (00, 01, or 10 for C.0, C.1, C.2 instruction formats, respectively). The `11` pattern is reserved for 32-bit instructions.

## 3. Impact on Pipeline Stages
### 3.1. Fetch Stage (`fetch_stage.sv`)
- **Instruction Fetch**: The fetch stage must be capable of fetching both 16-bit and 32-bit instructions from memory.
- **Instruction Length Detection**: The instruction length will be determined by inspecting the two least significant bits (LSBs) of the fetched instruction. If the LSBs are `11`, it's a 32-bit instruction; otherwise, it's a 16-bit RVC instruction.
- **Dynamic PC Increment**: The Program Counter (PC) increment logic needs to be dynamic. It will advance by 2 bytes for 16-bit RVC instructions and 4 bytes for standard 32-bit instructions, based on the detected instruction length.
- **Instruction Alignment**: Ensure proper instruction alignment for subsequent pipeline stages, potentially involving a buffer to handle misaligned fetches.

### 3.2. Decode Stage (`decode_stage.sv`)
- **Instruction Parsing**: The decode stage will be enhanced to directly parse both 16-bit RVC and 32-bit standard instruction formats. This involves using the instruction length information from the fetch stage to correctly interpret the instruction fields (opcode, funct3, funct7, register specifiers, immediate values).
- **Control Signal Generation**: Generate appropriate control signals based on the decoded RVC instruction, mapping them to the existing 32-bit instruction pipeline where possible.
- **Register File Access**: Correctly identify and access source and destination registers for RVC instructions.
- **Immediate Generation**: Extract and sign-extend immediate values from RVC instructions, which often have different immediate encoding schemes compared to 32-bit instructions.

## 4. Implementation Considerations
- **Instruction Buffer**: A small instruction buffer in the fetch stage might be beneficial to handle misaligned fetches or to provide a steady stream of instructions to the decode stage, especially if instruction lengths vary.
- **Instruction Decompression**: While direct parsing is planned, an alternative approach could involve decompressing RVC instructions into their 32-bit equivalents before entering the decode stage. This would simplify the decode logic but might add latency.
- **Hazard Detection**: Ensure that hazard detection and forwarding logic correctly account for RVC instructions, particularly if they modify register usage or introduce new dependencies.

## 5. Future Enhancements
- Full support for all RVC instruction extensions.
- Performance analysis of RVC impact on CPI and code density.