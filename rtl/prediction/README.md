
# RTL/Prediction Module Documentation

This directory contains the SystemVerilog modules related to branch prediction within the RISC-V core.

## Overview

The branch prediction unit (BPU) is crucial for maintaining pipeline efficiency by predicting the outcome of branch instructions, thereby reducing pipeline stalls due to control hazards. This module supports different types of branch predictors, configurable via parameters.

## Modules

### `tournament_predictor.sv`

This is the top-level module for the tournament branch predictor. It combines multiple prediction mechanisms (local, global) and a selector to choose the most accurate prediction. It instantiates the following sub-modules:

*   **`btb.sv` (Branch Target Buffer):** Caches the target addresses of recently taken branches.
*   **`local_predictor.sv`:** Implements a local branch predictor using a Branch History Table (BHT) to track the history of individual branches.
*   **`global_predictor.sv`:** Implements a global branch predictor using a Global History Register (GHR) and a Pattern History Table (PHT) to track the history of all branches.
*   **`selector.sv`:** Determines whether to use the prediction from the local or global predictor based on their past accuracy.

### `return_stack_buffer.sv`

A dedicated module for predicting return addresses of function calls. It operates as a small stack, pushing return addresses on `JAL` (jump and link) instructions and popping them on `JALR` (jump and link register) instructions.

### `branch_predictor.sv` (Legacy)

This module represents an older, simpler dynamic branch predictor that combines a basic BTB and BHT. It is retained for compatibility but is superseded by the `tournament_predictor.sv` for advanced prediction capabilities.

## Configuration

The type of branch predictor used in the RISC-V core can be configured via the `BRANCH_PREDICTOR_TYPE` parameter in `riscv_core.sv` and `fetch_stage.sv`. Supported values include:

*   `"TOURNAMENT"`: Utilizes the advanced tournament predictor (`tournament_predictor.sv`).
*   `"STATIC"`: Implements a simple static predictor (always predicts not-taken).
*   (Future) `"BIMODAL"` or `"GSHARE"`: Could be implemented using `branch_predictor.sv` or new modules.

## Integration

The branch prediction modules are primarily integrated within the `fetch_stage.sv` to determine the next Program Counter (PC). Updates to the predictors (actual branch outcomes) are provided from the `execute_stage.sv`.
