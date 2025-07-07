# Control Unit Architecture

## 1. Overview
The Control Unit is responsible for orchestrating the operation of the RISC-V pipeline by generating control signals for all functional units and managing hazards. It ensures correct instruction execution, handles pipeline stalls and flushes, and coordinates with the exception handling mechanism.

## 2. Key Components

### 2.1. Instruction Decoder (`decode_stage.sv`)
- **Purpose**: Interprets the instruction fetched from memory and generates raw control signals based on the instruction's opcode, funct3, and funct7 fields.
- **Functionality**:
    - Decodes standard RISC-V (RV32IM) instructions.
    - Generates immediate values for various instruction types.
    - Identifies source and destination registers.
    - Detects illegal instructions.
    - (Future: Decodes RVC compressed instructions).

### 2.2. Hazard Unit (`rtl/control/hazard_unit.sv`)
For a detailed architectural description of the Hazard Unit, refer to `docs/architecture/control/HAZARD_UNIT_ARCHITECTURE.md`.

### 2.3. Control Signal Distribution
- **Purpose**: Distributes the generated control signals to the appropriate functional units in each pipeline stage.
- **Mechanism**: Control signals are typically latched into pipeline registers (e.g., ID/EX, EX/MEM, MEM/WB) and propagate along with the data path.

### 2.4. Exception Handling Interface
- **Purpose**: Coordinates with the central exception handler to manage exceptions and interrupts.
- **Functionality**:
    - Receives exception signals from various pipeline stages (e.g., illegal instruction from Decode, memory access faults from Fetch/Memory).
    - Triggers pipeline flushes and PC redirection to the trap vector on exception.

## 3. Control Flow and Hazard Resolution

### 3.1. Data Hazards
- **RAW (Read After Write)**: Handled primarily by forwarding. The hazard unit monitors register dependencies and directs the correct data path.
- **Load-Use Hazards**: If a load instruction's result is needed by the very next instruction, a one-cycle stall is typically inserted as the data is not available for forwarding until the Memory stage completes.

### 3.2. Control Hazards
- **Branch/Jump Prediction**: The Fetch stage uses branch prediction (static currently, dynamic planned) to guess the next PC. The hazard unit monitors the actual outcome of branches in the Execute stage.
- **Misprediction Recovery**: If a branch is mispredicted, the hazard unit asserts a flush signal, clearing the incorrect instructions from the pipeline, and redirects the PC to the correct target.

### 3.3. Pipeline Stalls and Flushes
- **Stall Signals**: Propagated upstream to halt instruction fetching and decoding, preventing new instructions from entering the pipeline until a hazard is resolved.
- **Flush Signals**: Propagated downstream to invalidate instructions that are no longer valid due to a misprediction or exception, effectively turning them into NOPs.

## 4. Integration with Pipeline Stages

- **Fetch Stage**: Receives stall and flush signals, and PC redirect targets from the control unit.
- **Decode Stage**: Receives stall and flush signals, and provides decoded instruction information and register addresses.
- **Execute Stage**: Receives control signals for ALU operation, forwarding, and branch evaluation.
- **Memory Stage**: Receives control signals for memory read/write operations.
- **Writeback Stage**: Receives control signals for register write enable and write-back source selection.

## 5. Future Enhancements
- **Precise Exceptions**: Ensure that exceptions are handled precisely, meaning all instructions before the excepting instruction complete, and no instructions after it complete.
- **Out-of-Order Control**: For future Out-of-Order execution, the control unit will become significantly more complex, involving instruction issue logic, retirement logic, and interaction with the reorder buffer and reservation stations.
- **Advanced Hazard Detection**: More sophisticated hazard detection for complex pipelines.
