
`ifndef POWER_PKG_SV
`define POWER_PKG_SV

package power_pkg;

    import riscv_config_pkg::*;
    import riscv_types_pkg::*;

    typedef enum logic [2:0] {
        POWER_ACTIVE,
        POWER_IDLE,
        POWER_SLEEP,
        POWER_DEEP_SLEEP,
        POWER_THERMAL_THROTTLE
    } power_state_t;

    typedef struct packed {
        logic        aggressive_gating;
        logic        cache_gating_en;
        logic        retention_mode;
        logic        power_gating_en;
        logic [31:0] DEFAULT_IDLE_TIMEOUT;
        logic [31:0] DEFAULT_SLEEP_TIMEOUT;
    } power_config_t;

endpackage

`endif // POWER_PKG_SV
