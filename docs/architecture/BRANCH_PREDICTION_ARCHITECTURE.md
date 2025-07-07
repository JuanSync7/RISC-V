# Branch Prediction Architecture

## 1. Overview
Branch prediction is a crucial technique used in pipelined processors to minimize the performance penalty caused by control hazards (branches and jumps). This document describes the configurable branch prediction mechanisms implemented in the RISC-V core.

## 2. Current Branch Prediction Mechanisms

### 2.1. Configurable Prediction Strategy
The RISC-V core now supports configurable branch prediction strategies, selectable via the `BRANCH_PREDICTOR_TYPE` parameter:
- **Static Prediction**: All conditional branches are predicted as not-taken. The pipeline continues fetching instructions sequentially after the branch. This is a fallback or simple option.
- **Simple Dynamic Prediction**: Utilizes a basic Branch Target Buffer (BTB) and Branch History Table (BHT) with 2-bit saturating counters for improved accuracy over static prediction.
- **Tournament Prediction**: An advanced dynamic prediction mechanism that combines local and global prediction schemes for higher accuracy.

### 2.2. Branch Predictor Modules
- **`tournament_predictor.sv` (`rtl/prediction/tournament_predictor.sv`)**: This is the primary advanced dynamic branch predictor. It is a structural module that integrates:
    - `btb.sv`: Branch Target Buffer for caching target addresses.
    - `local_predictor.sv`: Implements a local predictor using a Branch History Table (BHT).
    - `global_predictor.sv`: Implements a global predictor using a Global History Register (GHR) and Pattern History Table (PHT).
    - `selector.sv`: Chooses between local and global predictions based on accuracy.
- **`return_stack_buffer.sv` (`rtl/prediction/return_stack_buffer.sv`)**: A dedicated module for predicting return addresses of function calls (e.g., JALR instructions). It complements the main branch predictor.
- **`branch_predictor.sv` (`rtl/prediction/branch_predictor.sv`)**: This module represents an older, simpler dynamic branch predictor. It is retained for compatibility but is superseded by the `tournament_predictor.sv` for advanced prediction capabilities.

### 2.3. Integration in Fetch Stage (`fetch_stage.sv`)
The `fetch_stage.sv` instantiates the selected branch predictor (based on `BRANCH_PREDICTOR_TYPE`) and the `return_stack_buffer` to determine the next Program Counter (PC):
- If a PC redirect (from a taken branch, jump, or exception) is asserted, it takes highest priority.
- Otherwise, if the selected branch predictor predicts taken and a BTB hit occurs, the predicted target is used.
- For `JALR` instructions, the `return_stack_buffer`'s prediction is prioritized.
- As a fallback (for static not-taken prediction or if no prediction is made), the PC is incremented by 4.

## 3. Implemented Dynamic Branch Prediction: Tournament Predictor

### 3.1. Goal Achieved
The core has been enhanced with advanced dynamic branch prediction capabilities through the implementation of a tournament predictor, significantly improving pipeline efficiency and reducing branch misprediction penalties.

### 3.2. Implemented Mechanisms
- **Branch History Table (BHT)**: Integrated within `local_predictor.sv`, using 2-bit saturating counters to predict future outcomes (taken/not-taken) based on per-branch history.
- **Branch Target Buffer (BTB)**: Implemented in `btb.sv`, caching target addresses of recently taken branches for fast lookup.
- **Global History Register (GHR) and Pattern History Table (PHT)**: Integrated within `global_predictor.sv`, using a global history of branches to predict outcomes.
- **Selector**: Implemented in `selector.sv`, dynamically choosing between the local and global predictor's output based on their past performance.
- **Return Address Stack (RAS)**: Implemented in `return_stack_buffer.sv`, a small stack to predict return addresses for function calls and returns.

### 3.3. Implementation Details
1.  **Refactored `tournament_predictor.sv`**: The original `tournament_predictor.sv` has been refactored into modular components (`btb.sv`, `local_predictor.sv`, `global_predictor.sv`, `selector.sv`) and now acts as a top-level structural module integrating these parts.
2.  **Updated Fetch Stage**: `fetch_stage.sv` now instantiates the refactored `tournament_predictor` and `return_stack_buffer`, leveraging their predictions for PC selection.
3.  **Misprediction Handling**: The pipeline includes robust misprediction detection and recovery mechanisms. When a misprediction occurs, the pipeline is flushed, and the correct PC is injected.
4.  **Branch Update Interface**: The `execute_stage.sv` provides the necessary `branch_update_t` information (actual outcome, target address, and instruction type) to train the branch predictors and update the RAS.

## 4. Performance Considerations

### 4.1. Metrics
- **Branch Prediction Accuracy**: Percentage of branches correctly predicted.
- **Misprediction Penalty**: Number of cycles lost due to a mispredicted branch.

### 4.2. Optimization Opportunities
- Increasing BTB/BHT/PHT/Selector size (via parameters).
- Implementing more sophisticated prediction algorithms (e.g., GShare, perceptron predictors) as future enhancements.
- Further integration with a branch target address cache (BTAC) for faster target delivery.

## 5. Testing and Verification

### 5.1. Test Scenarios
- Sequential code with no branches.
- Code with frequent conditional branches (loops, if-else).
- Code with unconditional jumps (JAL, JALR).
- Function calls and returns.
- Branches with varying prediction patterns (always taken, always not-taken, alternating).
- Stress testing with high branch rates.

### 5.2. Verification Checklist
- [X] Correct prediction for static branches.
- [X] Accurate prediction for dynamic branches (tournament predictor).
- [X] Correct PC redirection on taken branches/jumps.
- [X] Efficient pipeline flush on mispredictions.
- [X] BTB/BHT/PHT/Selector update logic correctness.
- [X] RAS functionality.

## 6. Future Enhancements
- Global History Register (GHR) for global branch prediction.
- Two-level adaptive predictors.
- Indirect branch prediction.
- Integration with a branch target address cache (BTAC).