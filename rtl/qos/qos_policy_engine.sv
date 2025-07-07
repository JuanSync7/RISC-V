`include "qos_pkg.sv"

module qos_policy_engine #(
    parameter CORE_ID = 0
) (
    input  logic                   clk_i,
    input  logic                   rst_ni,

    input  logic                   qos_enable_i,
    input  logic                   exception_pending_i,
    input  logic                   debug_access_pending_i,
    input  logic                   is_store_i, // From execute stage for data accesses
    input  logic                   is_critical_data_access_i, // From execute stage for data accesses

    output qos_config_t            instr_qos_config_o,
    output qos_config_t            data_qos_config_o
);

    // Internal signal for critical access pending
    logic critical_access_pending;
    assign critical_access_pending = exception_pending_i || debug_access_pending_i;

    // Function to generate instruction QoS configuration
    function automatic qos_config_t get_instruction_qos_config();
        qos_config_t qos_config;
        
        qos_config.qos_level = exception_pending_i ? QOS_LEVEL_CRITICAL : QOS_LEVEL_HIGH;
        qos_config.transaction_type = QOS_TYPE_INSTR_FETCH;
        qos_config.urgent = exception_pending_i;
        qos_config.guaranteed_bw = 1'b1;
        qos_config.weight = exception_pending_i ? QOS_WEIGHT_CRITICAL : QOS_WEIGHT_HIGH;
        qos_config.max_latency_cycles = exception_pending_i ? 16'd5 : 16'd25;
        qos_config.bandwidth_percent = 8'd30;
        qos_config.core_id = CORE_ID[3:0];
        qos_config.preemptable = ~exception_pending_i;
        qos_config.real_time = exception_pending_i;
        qos_config.retry_limit = 3'd1;
        qos_config.ordered = 1'b1;
        
        return qos_config;
    endfunction

    // Function to generate data QoS configuration
    function automatic qos_config_t get_data_qos_config(
        input logic is_store,
        input logic is_critical
    );
        qos_config_t qos_config;
        
        if (is_critical || exception_pending_i) begin
            qos_config.qos_level = QOS_LEVEL_CRITICAL;
            qos_config.weight = QOS_WEIGHT_CRITICAL;
            qos_config.max_latency_cycles = 16'd10;
            qos_config.urgent = 1'b1;
            qos_config.real_time = 1'b1;
            qos_config.preemptable = 1'b0;
        end else begin
            qos_config.qos_level = is_store ? QOS_LEVEL_MEDIUM : QOS_LEVEL_MEDIUM_HIGH;
            qos_config.weight = is_store ? QOS_WEIGHT_MEDIUM : QOS_WEIGHT_MEDIUM_HIGH;
            qos_config.max_latency_cycles = is_store ? 16'd100 : 16'd50;
            qos_config.urgent = 1'b0;
            qos_config.real_time = 1'b0;
            qos_config.preemptable = 1'b1;
        end
        
        qos_config.transaction_type = QOS_TYPE_DATA_ACCESS;
        qos_config.guaranteed_bw = is_critical || exception_pending_i;
        qos_config.bandwidth_percent = 8'd25;
        qos_config.core_id = CORE_ID[3:0];
        qos_config.retry_limit = 3'd2;
        qos_config.ordered = 1'b1;
        
        return qos_config;
    endfunction

    // Assign outputs based on QoS enable and policy functions
    always_comb begin
        if (qos_enable_i) begin
            instr_qos_config_o = get_instruction_qos_config();
            data_qos_config_o = get_data_qos_config(is_store_i, is_critical_data_access_i);
        end else begin
            // Default QoS configuration when disabled
            instr_qos_config_o = '0;
            data_qos_config_o = '0;
        end
    end

endmodule
