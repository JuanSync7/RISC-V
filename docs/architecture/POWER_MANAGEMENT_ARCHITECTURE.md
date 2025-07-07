# Power Management Architecture

## 1. Overview
This document details the architecture of the Power Management Unit (PMU) within the RISC-V system. The PMU is designed to optimize power consumption across the entire chip by implementing various power-saving techniques, including Dynamic Voltage and Frequency Scaling (DVFS), fine-grained clock gating, and comprehensive power state management.

## 2. Key Features
- **Dynamic Voltage and Frequency Scaling (DVFS)**: Adjusts voltage and frequency based on workload and thermal conditions.
- **Clock Gating**: Fine-grained control over clock distribution to inactive modules.
- **Power State Management**: Transitions the system through various power states (Active, Idle, Sleep, Deep Sleep, Thermal Throttling).
- **Power Domain Control**: Manages power-on/off and retention for independent power domains.
- **Thermal Management**: Responds to thermal alerts by throttling performance to prevent overheating.
- **Power Savings Estimation**: Provides real-time estimates of power savings.

## 3. PMU Module: `power_management.sv`

`power_management.sv` is the central module responsible for orchestrating all power management activities. It receives inputs from various system components (core activity, cache miss rates, temperature) and generates control signals for clock enables, voltage/frequency levels, and power domain states.

### 3.1. Module Parameters
- `NUM_CORES`: Number of cores managed.
- `NUM_POWER_DOMAINS`: Number of independent power domains.
- `NUM_VOLTAGE_LEVELS`: Number of discrete voltage levels for DVFS.
- `NUM_FREQ_LEVELS`: Number of discrete frequency levels for DVFS.

### 3.2. Inputs and Outputs (Key Signals)
- **Inputs**:
    - `clk_i`, `rst_ni`: System clock and reset.
    - `pm_enable_i`: Global power management enable.
    - `power_config_i`: Configuration struct for power management policies.
    - `core_active_i`, `core_idle_i`, `core_utilization_i`: Core activity and workload indicators.
    - `temperature_i`, `thermal_alert_i`: Thermal monitoring inputs.
    - `cache_miss_rate_i`, `cache_active_i`: Cache activity indicators.
- **Outputs**:
    - `core_clk_en_o`, `l2_cache_clk_en_o`, `l3_cache_clk_en_o`, `interconnect_clk_en_o`: Clock enable signals for various blocks.
    - `voltage_level_o`, `frequency_level_o`, `dvfs_update_o`: DVFS control signals.
    - `power_domain_en_o`, `retention_mode_o`: Power domain control signals.
    - `current_power_state_o`: Current system power state.
    - `power_savings_o`, `throttling_events_o`, `dvfs_transitions_o`: Performance monitoring outputs.

## 4. Functional Blocks

### 4.1. Power State Machine (FSM)
- **Purpose**: Manages the overall system power state transitions.
- **States**:
    - `POWER_ACTIVE`: Full performance, all units active.
    - `POWER_IDLE`: Cores/units are idle, aggressive clock gating, potential frequency reduction.
    - `POWER_SLEEP`: Deeper sleep, more aggressive power gating, retention possible.
    - `POWER_DEEP_SLEEP`: Minimal power consumption, most domains powered off, state saved.
    - `POWER_THERMAL_THROTTLE`: Performance reduced due to high temperature.
- **Transitions**: Based on activity levels, idle timeouts, thermal alerts, and explicit software commands.

#### 4.1.1. FSM Implementation
The FSM is implemented using a synchronous always_ff block for state updates and a combinational always_comb block for next-state logic.

```systemverilog
    power_state_t current_state_r, next_state_c;
    logic [15:0] state_timer_r;
    logic [31:0] idle_timeout_counter_r;
    
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_power_state_fsm
        if (!rst_ni) begin
            current_state_r <= POWER_ACTIVE;
            state_timer_r <= '0;
            idle_timeout_counter_r <= '0;
        end else begin
            current_state_r <= next_state_c;
            
            // State timing
            if (current_state_r != next_state_c) begin
                state_timer_r <= '0;
                idle_timeout_counter_r <= '0;
            end else begin
                state_timer_r <= state_timer_r + 1;
                if (current_state_r == POWER_IDLE) begin
                    idle_timeout_counter_r <= idle_timeout_counter_r + 1;
                end
            end
        end
    end
    
    always_comb begin : proc_power_state_logic
        next_state_c = current_state_r;
        
        // Thermal emergency always takes precedence
        if (thermal_alert_i) begin
            next_state_c = POWER_THERMAL_THROTTLE;
        end else begin
            case (current_state_r)
                POWER_ACTIVE: begin
                    if (pm_enable_i && (&core_idle_i)) begin
                        next_state_c = POWER_IDLE;
                    end
                end
                
                POWER_IDLE: begin
                    if (|core_active_i) begin
                        next_state_c = POWER_ACTIVE;
                    end else if (idle_timeout_counter_r > power_config_i.idle_timeout) begin
                        next_state_c = POWER_SLEEP;
                    end
                end
                
                POWER_SLEEP: begin
                    if (|core_active_i) begin
                        next_state_c = POWER_ACTIVE;
                    end else if (state_timer_r > power_config_i.sleep_timeout) begin
                        next_state_c = POWER_DEEP_SLEEP;
                    end
                end
                
                POWER_DEEP_SLEEP: begin
                    if (|core_active_i) begin
                        next_state_c = POWER_ACTIVE;
                    end
                end
                
                POWER_THERMAL_THROTTLE: begin
                    if (!thermal_alert_i && state_timer_r > 1000) begin
                        next_state_c = POWER_ACTIVE;
                    end
                end
                
                default: begin
                    next_state_c = POWER_ACTIVE;
                end
            endcase
        end
    end
```

### 4.2. Dynamic Voltage and Frequency Scaling (DVFS) Controller
- **Purpose**: Dynamically adjusts the operating voltage and frequency of the system based on workload and performance demand.
- **Mechanism**: Monitors core utilization, cache miss rates, and thermal conditions to determine the optimal voltage/frequency level. Implements hysteresis to prevent rapid oscillations.
- **Outputs**: `voltage_level_o` and `frequency_level_o` to external power management ICs/PLLs.

#### 4.2.1. DVFS Implementation

```systemverilog
    logic [2:0] target_voltage_r;
    logic [3:0] target_frequency_r;
    logic [31:0] dvfs_transition_count_r;
    logic dvfs_update_pending_r;
    
    // Workload Analysis for DVFS
    logic [31:0] average_utilization_c;
    logic [7:0] performance_demand_c;
    
    always_comb begin : proc_workload_analysis
        // Calculate average core utilization
        logic [31:0] total_utilization = '0;
        for (int i = 0; i < NUM_CORES; i++) begin
            total_utilization += core_utilization_i[i];
        end
        average_utilization_c = total_utilization / NUM_CORES;
        
        // Determine performance demand
        if (current_state_r == POWER_THERMAL_THROTTLE) begin
            performance_demand_c = 8'h20; // Low performance for thermal safety
        end else if (cache_miss_rate_i > 50) begin
            performance_demand_c = 8'hE0; // High performance for memory-bound workloads
        end else {
            performance_demand_c = average_utilization_c[7:0];
        end
    end
    
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_dvfs_controller
        if (!rst_ni) begin
            target_voltage_r <= 3'b100; // Mid-level voltage
            target_frequency_r <= 4'h8; // Mid-level frequency
            dvfs_transition_count_r <= '0;
            dvfs_update_pending_r <= 1'b0;
        end else begin
            logic [2:0] new_voltage;
            logic [3:0] new_frequency;
            
            // Determine optimal voltage/frequency based on performance demand
            case (performance_demand_c[7:4])
                4'h0, 4'h1: begin // Very low demand
                    new_voltage = 3'b001;
                    new_frequency = 4'h2;
                end
                4'h2, 4'h3: begin // Low demand
                    new_voltage = 3'b010;
                    new_frequency = 4'h4;
                end
                4'h4, 4'h5, 4'h6, 4'h7: begin // Medium demand
                    new_voltage = 3'b100;
                    new_frequency = 4'h8;
                end
                4'h8, 4'h9, 4'hA, 4'hB: begin // High demand
                    new_voltage = 3'b110;
                    new_frequency = 4'hC;
                end
                default: begin // Maximum demand
                    new_voltage = 3'b111;
                    new_frequency = 4'hF;
                end
            endcase
            
            // Apply hysteresis to prevent oscillation
            if ((new_voltage != target_voltage_r) || (new_frequency != target_frequency_r)) begin
                if (!dvfs_update_pending_r) begin
                    target_voltage_r <= new_voltage;
                    target_frequency_r <= new_frequency;
                    dvfs_update_pending_r <= 1'b1;
                    dvfs_transition_count_r <= dvfs_transition_count_r + 1;
                end
            end else begin
                dvfs_update_pending_r <= 1'b0;
            end
        end
    end
```

### 4.3. Clock Gating Control
- **Purpose**: Generates fine-grained clock enable signals for various functional blocks (cores, caches, interconnect) to reduce dynamic power consumption.
- **Mechanism**: Based on the current power state and activity indicators of individual units. For example, idle cores can have their clocks gated.

#### 4.3.1. Clock Gating Implementation

```systemverilog
    logic [NUM_CORES-1:0] core_clk_gate_r;
    logic l2_cache_clk_gate_r;
    logic l3_cache_clk_gate_r;
    logic interconnect_clk_gate_r;
    
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_clock_gating
        if (!rst_ni) begin
            core_clk_gate_r <= '1; // All clocks enabled initially
            l2_cache_clk_gate_r <= 1'b1;
            l3_cache_clk_gate_r <= 1'b1;
            interconnect_clk_gate_r <= 1'b1;
        end else begin
            // Per-core clock gating based on activity and power state
            for (int i = 0; i < NUM_CORES; i++) begin
                case (current_state_r)
                    POWER_ACTIVE: begin
                        core_clk_gate_r[i] <= core_active_i[i] || !power_config_i.aggressive_gating;
                    end
                    POWER_IDLE: begin
                        core_clk_gate_r[i] <= core_active_i[i];
                    end
                    POWER_SLEEP, POWER_DEEP_SLEEP: begin
                        core_clk_gate_r[i] <= 1'b0;
                    end
                    POWER_THERMAL_THROTTLE: begin
                        // Cycle cores for thermal management
                        core_clk_gate_r[i] <= (state_timer_r[3:0] == i) && core_active_i[i];
                    end
                    default: begin
                        core_clk_gate_r[i] <= core_active_i[i];
                    end
                endcase
            end
            
            // Cache clock gating
            case (current_state_r)
                POWER_ACTIVE, POWER_IDLE: begin
                    l2_cache_clk_gate_r <= |cache_active_i || !power_config_i.cache_gating_en;
                    l3_cache_clk_gate_r <= (cache_miss_rate_i > 10) || !power_config_i.cache_gating_en;
                end
                POWER_SLEEP: begin
                    l2_cache_clk_gate_r <= power_config_i.retention_mode;
                    l3_cache_clk_gate_r <= 1'b0;
                end
                POWER_DEEP_SLEEP: begin
                    l2_cache_clk_gate_r <= 1'b0;
                    l3_cache_clk_gate_r <= 1'b0;
                end
                default: begin
                    l2_cache_clk_gate_r <= |cache_active_i;
                    l3_cache_clk_gate_r <= |cache_active_i;
                end
            endcase
            
            // Interconnect clock gating
            interconnect_clk_gate_r <= (current_state_r == POWER_ACTIVE) || 
                                      (current_state_r == POWER_IDLE && |core_active_i);
        end
    end
```

### 4.4. Power Domain Management
- **Purpose**: Controls the power-on/off and retention states of independent power domains within the chip.
- **Mechanism**: Based on the system's current power state and configurable power gating policies. Supports retention mode for preserving state in low-power modes.

#### 4.4.1. Power Domain Management Implementation

```systemverilog
    logic [NUM_POWER_DOMAINS-1:0] power_domain_en_r;
    logic [NUM_POWER_DOMAINS-1:0] retention_mode_r;
    logic [31:0] throttling_event_count_r;
    
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_power_domains
        if (!rst_ni) begin
            power_domain_en_r <= '1; // All domains enabled initially
            retention_mode_r <= '0;
            throttling_event_count_r <= '0;
        end else begin
            // Core power domains (0 to NUM_CORES-1)
            for (int i = 0; i < NUM_CORES; i++) begin
                case (current_state_r)
                    POWER_ACTIVE: begin
                        power_domain_en_r[i] <= 1'b1;
                        retention_mode_r[i] <= 1'b0;
                    end
                    POWER_IDLE: begin
                        power_domain_en_r[i] <= core_active_i[i] || !power_config_i.power_gating_en;
                        retention_mode_r[i] <= !core_active_i[i] && power_config_i.retention_mode;
                    end
                    POWER_SLEEP: begin
                        power_domain_en_r[i] <= core_active_i[i];
                        retention_mode_r[i] <= !core_active_i[i];
                    end
                    POWER_DEEP_SLEEP: begin
                        power_domain_en_r[i] <= 1'b0;
                        retention_mode_r[i] <= power_config_i.retention_mode;
                    end
                    POWER_THERMAL_THROTTLE: begin
                        // Thermal throttling
                        power_domain_en_r[i] <= (state_timer_r[7:0] % NUM_CORES) == i;
                        retention_mode_r[i] <= 1'b0;
                        if ((state_timer_r[7:0] % NUM_CORES) == i && state_timer_r[7:0] != 0) begin
                            throttling_event_count_r <= throttling_event_count_r + 1;
                        end
                    end
                endcase
            end
            
            // Cache power domains (NUM_CORES to NUM_CORES+3)
            power_domain_en_r[NUM_CORES] <= l2_cache_clk_gate_r; // L2 domain
            power_domain_en_r[NUM_CORES+1] <= l3_cache_clk_gate_r; // L3 domain
            power_domain_en_r[NUM_CORES+2] <= interconnect_clk_gate_r; // Interconnect domain
            power_domain_en_r[NUM_CORES+3] <= (current_state_r != POWER_DEEP_SLEEP); // Peripheral domain
            
            // Retention modes for cache domains
            retention_mode_r[NUM_CORES] <= (current_state_r == POWER_SLEEP) && power_config_i.retention_mode;
            retention_mode_r[NUM_CORES+1] <= (current_state_r == POWER_SLEEP) && power_config_i.retention_mode;
            retention_mode_r[NUM_CORES+2] <= 1'b0; // Interconnect doesn't support retention
            retention_mode_r[NUM_CORES+3] <= (current_state_r == POWER_SLEEP) && power_config_i.retention_mode;
        end
    end
```

### 4.5. Power Savings Estimation
- **Purpose**: Provides an approximate real-time calculation of the power savings achieved by the PMU.
- **Mechanism**: Estimates savings based on the active clock gating, DVFS levels, and power-gated domains.

#### 4.5.1. Power Savings Estimation Implementation

```systemverilog
    logic [31:0] power_savings_estimate_r;
    
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_power_savings
        if (!rst_ni) begin
            power_savings_estimate_r <= '0;
        end else begin
            // Estimate power savings based on gated clocks and reduced voltage/frequency
            logic [31:0] clock_savings = 32'h0;
            logic [31:0] dvfs_savings = 32'h0;
            logic [31:0] domain_savings = 32'h0;
            
            // Clock gating savings (5-15% per gated domain)
            for (int i = 0; i < NUM_CORES; i++) begin
                if (!core_clk_gate_r[i]) clock_savings += 32'd10;
            end
            if (!l2_cache_clk_gate_r) clock_savings += 32'd15;
            if (!l3_cache_clk_gate_r) clock_savings += 32'd20;
            if (!interconnect_clk_gate_r) clock_savings += 32'd8;
            
            // DVFS savings (voltage scaling has cubic impact)
            case (target_voltage_r)
                3'b001: dvfs_savings = 32'd70; // Very low voltage
                3'b010: dvfs_savings = 32'd50; // Low voltage
                3'b100: dvfs_savings = 32'd0;  // Nominal voltage
                3'b110: dvfs_savings = 32'd0;  // High voltage (negative savings)
                3'b111: dvfs_savings = 32'd0;  // Max voltage (negative savings)
                default: dvfs_savings = 32'd0;
            endcase
            
            // Power domain savings
            for (int i = 0; i < NUM_POWER_DOMAINS; i++) begin
                if (!power_domain_en_r[i]) domain_savings += 32'd25;
                else if (retention_mode_r[i]) domain_savings += 32'd15;
            end
            
            power_savings_estimate_r <= (clock_savings + dvfs_savings + domain_savings) / 3;
        end
    end
```

## 5. Integration with System
- **Core Activity**: Receives activity and utilization signals from individual cores.
- **Cache Activity**: Receives miss rates and activity from the memory subsystem.
- **Thermal Sensors**: Interfaces with external thermal sensors for temperature readings.
- **External PMIC/PLL**: Outputs control signals for external Power Management ICs and PLLs to adjust voltage and frequency.
- **Software Interface**: Expected to be configurable via Control and Status Registers (CSRs) for software-driven power management policies.

## 6. Future Enhancements
- **Machine Learning-based Power Prediction**: Utilize ML models for more accurate workload prediction and proactive power adjustments.
- **Application-aware Power Management**: Tailor power policies based on the specific application running.
- **Advanced Thermal Management**: More sophisticated thermal models and response strategies.
- **Multi-core Power Coordination**: Enhanced coordination for power management in highly parallel systems.
- **Fine-grained Voltage Islands**: Support for more granular voltage domains.

## 5. Integration with System
- **Core Activity**: Receives activity and utilization signals from individual cores.
- **Cache Activity**: Receives miss rates and activity from the memory subsystem.
- **Thermal Sensors**: Interfaces with external thermal sensors for temperature readings.
- **External PMIC/PLL**: Outputs control signals for external Power Management ICs and PLLs to adjust voltage and frequency.
- **Software Interface**: Expected to be configurable via Control and Status Registers (CSRs) for software-driven power management policies.

## 6. Future Enhancements
- **Machine Learning-based Power Prediction**: Utilize ML models for more accurate workload prediction and proactive power adjustments.
- **Application-aware Power Management**: Tailor power policies based on the specific application running.
- **Advanced Thermal Management**: More sophisticated thermal models and response strategies.
- **Multi-core Power Coordination**: Enhanced coordination for power management in highly parallel systems.
- **Fine-grained Voltage Islands**: Support for more granular voltage domains.
