`include "qos_pkg.sv"

module qos_monitor #(
    parameter CORE_ID = 0
) (
    input  logic                   clk_i,
    input  logic                   rst_ni,

    input  logic                   qos_enable_i,
    input  logic                   mem_req_valid_i, // From arbitration unit
    input  logic                   mem_req_ready_i, // From external memory system
    input  qos_config_t            granted_qos_config_i, // Granted QoS config from arbiter
    input  logic                   granted_valid_i, // Valid signal for granted_qos_config_i

    output logic [31:0]            qos_violations_o
);

    logic [31:0] qos_violation_counter;

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_qos_monitoring
        if (!rst_ni) begin
            qos_violation_counter <= 0;
        end else begin
            if (qos_enable_i) begin
                // Monitor for basic QoS violations: memory not ready when request is valid
                if (mem_req_valid_i && !mem_req_ready_i) begin
                    qos_violation_counter <= qos_violation_counter + 1;
                end

                // TODO: Add more sophisticated violation monitoring here:
                // - Latency deadline misses (using granted_qos_config_i.max_latency_cycles)
                // - Bandwidth violations (using granted_qos_config_i.bandwidth_percent)
                // - Preemption violations
                // - Retry limit exceeded
            end
        end
    end

    assign qos_violations_o = qos_violation_counter;

endmodule
