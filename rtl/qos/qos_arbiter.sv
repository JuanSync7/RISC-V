import riscv_config_pkg::*;
import riscv_core_pkg::*;
`include "qos_pkg.sv"

module qos_arbiter #(
    parameter NUM_REQUESTERS = MAX_CORES
) (
    input  logic                   clk_i,
    input  logic                   rst_ni,

    input  qos_config_t            qos_config_i [NUM_REQUESTERS-1:0],
    input  logic                   req_valid_i    [NUM_REQUESTERS-1:0],
    output logic                   req_ready_o    [NUM_REQUESTERS-1:0],
    output logic [NUM_REQUESTERS-1:0] grant_o,
    output qos_config_t            granted_qos_config_o
);

    // Internal signals
    logic [NUM_REQUESTERS-1:0]      priority;
    logic [NUM_REQUESTERS-1:0]      req_active;
    logic [NUM_REQUESTERS-1:0]      grant_internal;

    // Determine active requests
    assign req_active = req_valid_i;

    // Priority encoding (example: higher QoS level = higher priority)
    // This is a simple priority encoder. More complex arbitration can be added here.
    genvar i;
    generate
        for (i = 0; i < NUM_REQUESTERS; i++) begin : gen_priority
            always_comb begin
                case (qos_config_i[i].qos_level)
                    QOS_LEVEL_CRITICAL:    priority[i] = 2'b11;
                    QOS_LEVEL_HIGH:        priority[i] = 2'b10;
                    QOS_LEVEL_MEDIUM_HIGH: priority[i] = 2'b01;
                    default:               priority[i] = 2'b00; // QOS_LEVEL_MEDIUM
                endcase
            end
        end
    endgenerate

    // Simple fixed-priority arbitration (highest priority wins)
    // If multiple requests have the same highest priority, the one with the lowest index wins.
    always_comb begin
        grant_internal = '0;
        granted_qos_config_o = '0; // Default to all zeros

        for (int p = 3; p >= 0; p--) begin // Iterate through priority levels (assuming 4 levels based on qos_level_t)
            for (int j = 0; j < NUM_REQUESTERS; j++) begin
                if (req_active[j] && priority[j] == p) begin
                    grant_internal[j] = 1'b1;
                    granted_qos_config_o = qos_config_i[j];
                    break; // Grant to the first requester found at this priority level
                end
            end
            if (|grant_internal) break; // If a grant was made, stop searching
        end
    end

    assign grant_o = grant_internal;

    // Ready signal generation
    // A requester is ready if it is granted and the arbiter is ready to accept the request.
    // For this simple arbiter, we assume the arbiter is always ready if a grant is made.
    generate
        for (i = 0; i < NUM_REQUESTERS; i++) begin : gen_req_ready
            assign req_ready_o[i] = grant_o[i];
        end
    endgenerate

endmodule
