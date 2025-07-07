package qos_pkg;

  // QoS Levels
  typedef enum logic [1:0] {
    QOS_LEVEL_CRITICAL      = 2'b11,
    QOS_LEVEL_HIGH          = 2'b10,
    QOS_LEVEL_MEDIUM_HIGH   = 2'b01,
    QOS_LEVEL_MEDIUM        = 2'b00
  } qos_level_t;

  // QoS Weights
  typedef enum logic [1:0] {
    QOS_WEIGHT_CRITICAL     = 2'b11,
    QOS_WEIGHT_HIGH         = 2'b10,
    QOS_WEIGHT_MEDIUM_HIGH  = 2'b01,
    QOS_WEIGHT_MEDIUM       = 2'b00
  } qos_weight_t;

  // Transaction Types
  typedef enum logic [1:0] {
    QOS_TYPE_INSTR_FETCH    = 2'b00,
    QOS_TYPE_DATA_ACCESS    = 2'b01
  } qos_transaction_type_t;

  // QoS Configuration Structure
  typedef struct packed {
    qos_level_t             qos_level;          // Quality of Service level
    qos_transaction_type_t  transaction_type;   // Type of transaction (instruction fetch, data access)
    logic                   urgent;             // Indicates an urgent transaction
    logic                   guaranteed_bw;      // Indicates guaranteed bandwidth requirement
    qos_weight_t            weight;             // Weight for arbitration
    logic [15:0]            max_latency_cycles; // Maximum allowed latency in cycles
    logic [7:0]             bandwidth_percent;  // Percentage of bandwidth required
    logic [3:0]             core_id;            // Core ID originating the request
    logic                   preemptable;        // Indicates if the transaction can be preempted
    logic                   real_time;          // Indicates a real-time transaction
    logic [2:0]             retry_limit;        // Number of retries allowed
    logic                   ordered;            // Indicates if ordering is required
  } qos_config_t;

endpackage
