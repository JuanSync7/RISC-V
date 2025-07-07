import riscv_config_pkg::*;
import riscv_core_pkg::*;
`include "qos_pkg.sv"
`include "qos_arbiter.sv"
`include "qos_monitor.sv"
`include "qos_policy_engine.sv"

module qos_management_unit #(
    parameter CORE_ID = 0,
    parameter NUM_REQUESTERS = 2 // Example: 0 for instruction, 1 for data
) (
    input  logic                   clk_i,
    input  logic                   rst_ni,

    input  logic                   qos_enable_i,
    input  logic                   exception_pending_i,
    input  logic                   debug_access_pending_i,
    input  logic                   is_store_i, // From execute stage for data accesses
    input  logic                   is_critical_data_access_i, // From execute stage for data accesses

    // Inputs from core for arbitration
    input  qos_config_t            req_qos_config_i [NUM_REQUESTERS-1:0],
    input  logic                   req_valid_i    [NUM_REQUESTERS-1:0],
    output logic                   req_ready_o    [NUM_REQUESTERS-1:0],

    // Inputs from external memory system for monitoring
    input  logic                   mem_req_valid_i, // From arbitration unit
    input  logic                   mem_req_ready_i, // From external memory system

    // Outputs to core
    output logic [NUM_REQUESTERS-1:0] granted_req_o,
    output qos_config_t            granted_qos_config_o,
    output logic [31:0]            qos_violations_o
);

    // Internal signals for connecting sub-modules
    qos_config_t instr_qos_config;
    qos_config_t data_qos_config;

    // Instantiate QoS Policy Engine
    qos_policy_engine #(
        .CORE_ID(CORE_ID)
    ) i_qos_policy_engine (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .qos_enable_i(qos_enable_i),
        .exception_pending_i(exception_pending_i),
        .debug_access_pending_i(debug_access_pending_i),
        .is_store_i(is_store_i),
        .is_critical_data_access_i(is_critical_data_access_i),
        .instr_qos_config_o(instr_qos_config),
        .data_qos_config_o(data_qos_config)
    );

    // Instantiate QoS Arbiter
    qos_arbiter #(
        .NUM_REQUESTERS(NUM_REQUESTERS)
    ) i_qos_arbiter (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .qos_config_i(req_qos_config_i),
        .req_valid_i(req_valid_i),
        .req_ready_o(req_ready_o),
        .grant_o(granted_req_o),
        .granted_qos_config_o(granted_qos_config_o)
    );

    // Instantiate QoS Monitor
    qos_monitor #(
        .CORE_ID(CORE_ID)
    ) i_qos_monitor (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .qos_enable_i(qos_enable_i),
        .mem_req_valid_i(mem_req_valid_i),
        .mem_req_ready_i(mem_req_ready_i),
        .granted_qos_config_i(granted_qos_config_o),
        .granted_valid_i(|granted_req_o), // Granted config is valid if any request is granted
        .qos_violations_o(qos_violations_o)
    );

endmodule
