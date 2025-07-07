# Functional Units Architecture

## 1. Overview
This document describes the architecture of the core functional units within the RISC-V processor. These units are responsible for executing various types of instructions, performing arithmetic, logical, and memory operations, and managing control and status registers. Each unit is designed as a modular component with well-defined interfaces for integration into the pipeline.

## 2. Key Functional Units

### 2.1. Arithmetic Logic Unit (ALU) (`alu.sv`)
- **Purpose**: Performs all integer arithmetic and logical operations.
- **Key Features**:
    - Supports standard RISC-V arithmetic operations (ADD, SUB, SLT, SLTU).
    - Supports logical operations (AND, OR, XOR).
    - Supports shift operations (SLL, SRL, SRA).
    - Generates zero and overflow flags.
- **Interface**: Takes two operands and an ALU operation code, outputs a result and status flags.
- **Integration**: Primarily used in the Execute stage of the pipeline.

#### 2.1.1. ALU Implementation Details
The ALU is a purely combinational module. The core logic is implemented using a `case` statement that selects the operation based on the `alu_op_e` input. Overflow detection for ADD and SUB operations is also included.

```systemverilog
module alu #(
    parameter integer DATA_WIDTH = XLEN
)(
    input  alu_op_e alu_op_i,
    input  word_t   operand_a_i,
    input  word_t   operand_b_i,
    output word_t   alu_result_o,
    output logic    zero_o,
    output logic    overflow_o
);

    logic [DATA_WIDTH-1:0] alu_result;
    logic add_overflow, sub_overflow;

    always_comb begin
        alu_result = 'x;
        case (alu_op_i)
            ALU_OP_ADD:  alu_result = operand_a_i + operand_b_i;
            ALU_OP_SUB:  alu_result = operand_a_i - operand_b_i;
            ALU_OP_XOR:  alu_result = operand_a_i ^ operand_b_i;
            ALU_OP_OR:   alu_result = operand_a_i | operand_b_i;
            ALU_OP_AND:  alu_result = operand_a_i & operand_b_i;
            ALU_OP_SLL:  alu_result = operand_a_i << operand_b_i[4:0];
            ALU_OP_SRL:  alu_result = operand_a_i >> operand_b_i[4:0];
            ALU_OP_SRA:  alu_result = $signed(operand_a_i) >>> operand_b_i[4:0];
            ALU_OP_SLT:  alu_result = ($signed(operand_a_i) < $signed(operand_b_i)) ? 32'd1 : 32'd0;
            ALU_OP_SLTU: alu_result = (operand_a_i < operand_b_i) ? 32'd1 : 32'd0;
            ALU_OP_LUI:  alu_result = operand_b_i;
            ALU_OP_COPY_A: alu_result = operand_a_i;
            ALU_OP_COPY_B: alu_result = operand_b_i;
            default:     alu_result = 'x;
        endcase
    end

    always_comb begin
        add_overflow = 1'b0;
        sub_overflow = 1'b0;
        
        if (alu_op_i == ALU_OP_ADD) begin
            add_overflow = (operand_a_i[DATA_WIDTH-1] == operand_b_i[DATA_WIDTH-1]) && 
                          (alu_result[DATA_WIDTH-1] != operand_a_i[DATA_WIDTH-1]);
        end else if (alu_op_i == ALU_OP_SUB) begin
            sub_overflow = (operand_a_i[DATA_WIDTH-1] != operand_b_i[DATA_WIDTH-1]) && 
                          (alu_result[DATA_WIDTH-1] == operand_b_i[DATA_WIDTH-1]);
        end
    end

    assign alu_result_o = alu_result;
    assign zero_o       = (alu_result == '0);
    assign overflow_o   = add_overflow || sub_overflow;

endmodule
```

### 2.2. Register File (`reg_file.sv`)
- **Purpose**: Stores the 32 general-purpose integer registers (x0-x31) of the RISC-V architecture.
- **Key Features**:
    - Dual read ports for simultaneous operand fetching.
    - Single write port for result write-back.
    - Register x0 is hardwired to zero.
    - Supports hazard detection and forwarding (in conjunction with the Hazard Unit).
- **Interface**: Inputs for read addresses, write address, write data, and write enable; outputs for read data.
- **Integration**: Read in the Decode stage, written to in the Writeback stage.

#### 2.2.1. Register File Implementation Details
The register file is implemented as an array of `word_t` (32-bit) registers. It features two asynchronous read ports and one synchronous write port. Writes to register `x0` (address 0) are ignored, and reads from `x0` always return zero, adhering to the RISC-V specification.

```systemverilog
module reg_file #(
    parameter integer DATA_WIDTH = XLEN,
    parameter integer REG_COUNT = REG_COUNT,
    parameter integer REG_ADDR_WIDTH = REG_ADDR_WIDTH
)(
    input  logic        clk_i,
    input  logic        rst_ni,
    input  logic        write_en_i,
    input  reg_addr_t   rd_addr_i,
    input  word_t       rd_data_i,
    input  reg_addr_t   rs1_addr_i,
    output word_t       rs1_data_o,
    input  reg_addr_t   rs2_addr_i,
    output word_t       rs2_data_o
);

    word_t registers[REG_COUNT];

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            for (int i = 0; i < REG_COUNT; i++) begin
                registers[i] <= '0;
            end
        end else begin
            if (write_en_i && (rd_addr_i != '0)) begin
                registers[rd_addr_i] <= rd_data_i;
            end
        end
    end

    assign rs1_data_o = (rs1_addr_i == '0) ? '0 : registers[rs1_addr_i];
    assign rs2_data_o = (rs2_addr_i == '0) ? '0 : registers[rs2_addr_i];

`ifndef SYNTHESIS
    property p_no_write_to_x0;
        @(posedge clk_i)
        disable iff(!rst_ni)
        !(write_en_i && (rd_addr_i == '0));
    endproperty

    a_no_write_to_x0: assert property(p_no_write_to_x0) else
        $error("Assertion failed: Attempted to write to register x0.");
`endif

endmodule
```

### 2.3. Multiplier Unit (`mult_unit.sv`)
- **Purpose**: Performs integer multiplication operations as part of the RISC-V M-extension.
- **Key Features**:
    - Supports signed and unsigned multiplication.
    - Generates both high and low parts of the 64-bit product.
    - Multi-cycle operation with busy and done signals.
- **Interface**: Inputs for two operands, start signal, and operation type; outputs for high/low results, busy, and done status.
- **Integration**: Used in the Execute stage for multiplication instructions.

#### 2.3.1. Multiplier Implementation Details
The `mult_unit` is a pipelined module that performs multiplication. It takes two 32-bit operands and an operation type, and produces a 32-bit result (either the lower or upper 32 bits of the 64-bit product). The latency of the pipeline is configurable. The `busy_q` register acts as a shift register to track the progress of the operation through the pipeline.

```systemverilog
module mult_unit #(
    parameter integer DATA_WIDTH = XLEN,
    parameter integer LATENCY    = DEFAULT_MULT_LATENCY
) (
    input  logic        clk_i,
    input  logic        rst_ni,
    input  logic        start_i,
    input  logic [2:0]  op_type_i,
    input  word_t       operand_a_i,
    input  word_t       operand_b_i,
    output word_t       result_o,
    output logic        done_o,
    output logic        exception_valid_o,
    output logic [31:0] exception_cause_o
);

    localparam logic [2:0] OP_TYPE_MUL    = 3'b000;
    localparam logic [2:0] OP_TYPE_MULH   = 3'b001;
    localparam logic [2:0] OP_TYPE_MULHSU = 3'b010;
    localparam logic [2:0] OP_TYPE_MULHU  = 3'b011;

    word_t      operand_a_q, operand_b_q;
    logic [2:0] op_type_q;

    logic [63:0] product_ss;
    logic [63:0] product_su;
    logic [63:0] product_uu;

    logic [LATENCY-1:0] busy_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            operand_a_q <= '0;
            operand_b_q <= '0;
            op_type_q   <= '0;
        end else if (start_i) begin
            operand_a_q <= operand_a_i;
            operand_b_q <= operand_b_i;
            op_type_q   <= op_type_i;
        end
    end

    assign product_ss = $signed(operand_a_q) * $signed(operand_b_q);
    assign product_su = $signed(operand_a_q) * operand_b_q;
    assign product_uu = operand_a_q * operand_b_q;

    always_comb begin
        case (op_type_q)
            OP_TYPE_MUL:    result_o = product_ss[DATA_WIDTH-1:0];
            OP_TYPE_MULH:   result_o = product_ss[2*DATA_WIDTH-1:DATA_WIDTH];
            OP_TYPE_MULHSU: result_o = product_su[2*DATA_WIDTH-1:DATA_WIDTH];
            OP_TYPE_MULHU:  result_o = product_uu[2*DATA_WIDTH-1:DATA_WIDTH];
            default:        result_o = '0;
        endcase
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            busy_q <= '0;
        end else begin
            if (start_i) begin
                busy_q <= {1'b1, {LATENCY-1{1'b0}}};
            end else begin
                busy_q <= {1'b0, busy_q[LATENCY-1:1]};
            end
        end
    end

    assign done_o = busy_q[0];
    assign exception_valid_o = 1'b0;
    assign exception_cause_o = '0;

endmodule
```

#### 2.3.1. Multiplier Implementation Details
The `mult_unit` is a pipelined module that performs multiplication. It takes two 32-bit operands and an operation type, and produces a 32-bit result (either the lower or upper 32 bits of the 64-bit product). The latency of the pipeline is configurable. The `busy_q` register acts as a shift register to track the progress of the operation through the pipeline.

```systemverilog
module mult_unit #(
    parameter integer DATA_WIDTH = XLEN,
    parameter integer LATENCY    = DEFAULT_MULT_LATENCY
) (
    input  logic        clk_i,
    input  logic        rst_ni,
    input  logic        start_i,
    input  logic [2:0]  op_type_i,
    input  word_t       operand_a_i,
    input  word_t       operand_b_i,
    output word_t       result_o,
    output logic        done_o,
    output logic        exception_valid_o,
    output logic [31:0] exception_cause_o
);

    localparam logic [2:0] OP_TYPE_MUL    = 3'b000;
    localparam logic [2:0] OP_TYPE_MULH   = 3'b001;
    localparam logic [2:0] OP_TYPE_MULHSU = 3'b010;
    localparam logic [2:0] OP_TYPE_MULHU  = 3'b011;

    word_t      operand_a_q, operand_b_q;
    logic [2:0] op_type_q;

    logic [63:0] product_ss;
    logic [63:0] product_su;
    logic [63:0] product_uu;

    logic [LATENCY-1:0] busy_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            operand_a_q <= '0;
            operand_b_q <= '0;
            op_type_q   <= '0;
        end else if (start_i) begin
            operand_a_q <= operand_a_i;
            operand_b_q <= operand_b_i;
            op_type_q   <= op_type_i;
        end
    end

    assign product_ss = $signed(operand_a_q) * $signed(operand_b_q);
    assign product_su = $signed(operand_a_q) * operand_b_q;
    assign product_uu = operand_a_q * operand_b_q;

    always_comb begin
        case (op_type_q)
            OP_TYPE_MUL:    result_o = product_ss[DATA_WIDTH-1:0];
            OP_TYPE_MULH:   result_o = product_ss[2*DATA_WIDTH-1:DATA_WIDTH];
            OP_TYPE_MULHSU: result_o = product_su[2*DATA_WIDTH-1:DATA_WIDTH];
            OP_TYPE_MULHU:  result_o = product_uu[2*DATA_WIDTH-1:DATA_WIDTH];
            default:        result_o = '0;
        endcase
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            busy_q <= '0;
        end else begin
            if (start_i) begin
                busy_q <= {1'b1, {LATENCY-1{1'b0}}};
            end else begin
                busy_q <= {1'b0, busy_q[LATENCY-1:1]};
            end
        end
    end

    assign done_o = busy_q[0];
    assign exception_valid_o = 1'b0;
    assign exception_cause_o = '0;

endmodule
```

### 2.4. Divider Unit (`div_unit.sv`)
- **Purpose**: Performs integer division and remainder operations as part of the RISC-V M-extension.
- **Key Features**:
    - Supports signed and unsigned division.
    - Calculates both quotient and remainder.
    - Multi-cycle operation with busy and done signals.
    - Detects and signals division-by-zero errors.
- **Interface**: Inputs for dividend, divisor, start signal, and operation type; outputs for quotient, remainder, busy, done, and division-by-zero status.
- **Integration**: Used in the Execute stage for division instructions.

#### 2.4.1. Divider Implementation Details
The `div_unit` is a pipelined module that performs division and remainder calculations. It handles both signed and unsigned operations and detects division-by-zero and signed overflow conditions, generating exceptions as per the RISC-V specification. The latency of the pipeline is configurable.

```systemverilog
module div_unit #(
    parameter integer DATA_WIDTH = XLEN,
    parameter integer LATENCY    = DEFAULT_DIV_LATENCY
) (
    input  logic        clk_i,
    input  logic        rst_ni,
    input  logic        start_i,
    input  logic [2:0]  op_type_i,
    input  word_t       operand_a_i,
    input  word_t       operand_b_i,
    output word_t       result_o,
    output logic        done_o,
    output logic        busy_o,
    output logic        exception_valid_o,
    output logic [31:0] exception_cause_o
);

    localparam logic [2:0] OP_TYPE_DIV  = 3'b100;
    localparam logic [2:0] OP_TYPE_DIVU = 3'b101;
    localparam logic [2:0] OP_TYPE_REM  = 3'b110;
    localparam logic [2:0] OP_TYPE_REMU = 3'b111;

    word_t      operand_a_q, operand_b_q;
    logic [2:0] op_type_q;

    word_t div_result_signed;
    word_t div_result_unsigned;
    word_t rem_result_signed;
    word_t rem_result_unsigned;

    logic [LATENCY-1:0] busy_q;

    logic div_by_zero;
    logic signed_overflow;
    logic use_default_result;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            operand_a_q <= '0;
            operand_b_q <= '0;
            op_type_q   <= '0;
        end else if (start_i) begin
            operand_a_q <= operand_a_i;
            operand_b_q <= operand_b_i;
            op_type_q   <= op_type_i;
        end
    end

    assign div_by_zero = (operand_b_q == '0);
    assign signed_overflow = (operand_a_q == {1'b1, {(DATA_WIDTH-1){1'b0}}}) && (operand_b_q == {DATA_WIDTH{1'b1}});
    assign use_default_result = div_by_zero || signed_overflow;

    assign exception_valid_o = use_default_result;
    always_comb begin
        if (div_by_zero) begin
            exception_cause_o = CAUSE_ILLEGAL_INSTRUCTION;
        end else if (signed_overflow) begin
            exception_cause_o = CAUSE_ILLEGAL_INSTRUCTION;
        end else begin
            exception_cause_o = '0;
        end
    end

    assign div_result_signed   = ($signed(operand_a_q) / $signed(operand_b_q));
    assign div_result_unsigned = (operand_a_q / operand_b_q);
    assign rem_result_signed   = ($signed(operand_a_q) % $signed(operand_b_q));
    assign rem_result_unsigned = (operand_a_q % operand_b_q);

    always_comb begin
        if (use_default_result) begin
            case (op_type_q)
                OP_TYPE_DIV:  result_o = div_by_zero ? {DATA_WIDTH{1'b1}} : operand_a_q;
                OP_TYPE_DIVU: result_o = {DATA_WIDTH{1'b1}};
                OP_TYPE_REM:  result_o = div_by_zero ? operand_a_q : '0;
                OP_TYPE_REMU: result_o = operand_a_q;
                default:      result_o = '0;
            endcase
        end else begin
            case (op_type_q)
                OP_TYPE_DIV:  result_o = div_result_signed;
                OP_TYPE_DIVU: result_o = div_result_unsigned;
                OP_TYPE_REM:  result_o = rem_result_signed;
                OP_TYPE_REMU: result_o = rem_result_unsigned;
                default:      result_o = '0;
            endcase
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            busy_q <= '0;
        end else begin
            if (start_i) begin
                busy_q <= {{(LATENCY-1){1'b0}}, 1'b1};
            end else begin
                busy_q <= {busy_q[LATENCY-2:0], 1'b0};
            end
        end
    end

    assign done_o = busy_q[LATENCY-1];
    assign busy_o = |busy_q;

endmodule
```

### 2.5. Control and Status Register (CSR) File (`csr_regfile.sv`)
- **Purpose**: Implements the Control and Status Registers (CSRs) as defined by the RISC-V privileged architecture specification.
- **Key Features**:
    - Stores and manages machine-mode CSRs (e.g., `mstatus`, `mepc`, `mcause`, `mtvec`).
    - Handles CSR read and write operations.
    - Supports privilege level checking for CSR access.
    - Integrates with the exception handling mechanism for trap entry/return.
- **Interface**: Inputs for CSR address, data, write enable, and privilege level; outputs for read data and illegal access indication.
- **Integration**: Accessed by the Execute stage for CSR instructions and by the Exception Handler for context saving/restoring.

#### 2.5.1. CSR Register File Implementation Details
The `csr_regfile` module manages the Machine-mode Control and Status Registers. It supports atomic read-write, read-set, and read-clear operations as defined by the RISC-V ISA. Trap handling (exceptions and interrupts) and `MRET` instructions trigger specific updates to CSRs like `mstatus`, `mepc`, `mcause`, and `mtval`. The module also includes free-running `mcycle` and `minstret` counters.

```systemverilog
module csr_regfile
#(
    parameter word_t HART_ID = 32'd0
)
(
    input  logic        clk_i,
    input  logic        rst_ni,
    input  logic        instruction_retired_i,
    input  logic [11:0] csr_addr_i,
    input  logic [2:0]  csr_op_i,
    input  logic        write_en_i,
    input  word_t       rs1_data_i,
    output word_t       read_data_o,
    input  logic        trap_en_i,
    input  logic        mret_en_i,
    input  addr_t       mepc_i,
    input  word_t       mcause_i,
    input  word_t       mtval_i,
    output addr_t       mepc_o,
    output addr_t       mtvec_o,
    output word_t       mstatus_o,
    output word_t       mie_o,
    output word_t       mip_o,
    output word_t       mcause_o,
    output word_t       mtval_o,
    output logic        mstatus_mie_o,
    output logic [1:0]  mtvec_mode_o,
    output addr_t       mtvec_base_o,
    input  logic [NUM_CORES-1:0]    l1_icache_hit_i,
    input  logic        pipeline_stall_i
);

    localparam logic [2:0] CSR_OP_RW = 3'b001;
    localparam logic [2:0] CSR_OP_RS = 3'b010;
    localparam logic [2:0] CSR_OP_RC = 3'b011;

    localparam word_t MISA_RESET_VAL = 32'h40001101;

    localparam logic [11:0] MCYCLE_ADDR    = 12'hB00;
    localparam logic [11:0] MINSTRET_ADDR  = 12'hB02;
    localparam logic [11:0] MCYCLEH_ADDR   = 12'hB80;
    localparam logic [11:0] MINSTRETH_ADDR = 12'hB82;

    word_t mstatus_q, misa_q, mie_q, mtvec_q, mscratch_q, mepc_q, mcause_q, mtval_q, mip_q;
    word_t mhartid_q;
    logic [63:0] mcycle_q;
    logic [63:0] minstret_q;

    always_comb begin
        case (csr_addr_i)
            MSTATUS_ADDR:  read_data_o = mstatus_q;
            MISA_ADDR:     read_data_o = misa_q;
            MIE_ADDR:      read_data_o = mie_q;
            MTVEC_ADDR:    read_data_o = mtvec_q;
            MSCRATCH_ADDR: read_data_o = mscratch_q;
            MEPC_ADDR:     read_data_o = mepc_q;
            MCAUSE_ADDR:   read_data_o = mcause_q;
            MTVAL_ADDR:    read_data_o = mtval_q;
            MIP_ADDR:      read_data_o = mip_q;
            MHARTID_ADDR:  read_data_o = mhartid_q;
            MCYCLE_ADDR:    read_data_o = mcycle_q[31:0];
            MINSTRET_ADDR:  read_data_o = minstret_q[31:0];
            MCYCLEH_ADDR:   read_data_o = mcycle_q[63:32];
            MINSTRETH_ADDR: read_data_o = minstret_q[63:32];
            default:       read_data_o = '0;
        endcase
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            mstatus_q  <= '0;
            misa_q     <= MISA_RESET_VAL;
            mie_q      <= '0;
            mtvec_q    <= '0;
            mscratch_q <= '0;
            mepc_q     <= '0;
            mcause_q   <= '0;
            mtval_q    <= '0;
            mip_q      <= '0;
            mhartid_q  <= HART_ID;
            mcycle_q   <= '0;
            minstret_q <= '0;
        end else begin
            mcycle_q <= mcycle_q + 1;
            if (instruction_retired_i) begin
                minstret_q <= minstret_q + 1;
            end

            if (trap_en_i) begin
                mepc_q    <= mepc_i;
                mcause_q  <= mcause_i;
                mtval_q   <= mtval_i;
                mstatus_q <= {mstatus_q[31:8], mstatus_q[3], mstatus_q[6:4], 1'b0, mstatus_q[2:0]};
            end else if (mret_en_i) begin
                mstatus_q <= {mstatus_q[31:8], 1'b1, mstatus_q[6:4], mstatus_q[7], mstatus_q[2:0]};
            end else if (write_en_i) begin
                case (csr_addr_i)
                    MSTATUS_ADDR:  mstatus_q  <= csr_op(mstatus_q, rs1_data_i, csr_op_i);
                    MIE_ADDR:      mie_q      <= csr_op(mie_q, rs1_data_i, csr_op_i);
                    MTVEC_ADDR:    mtvec_q    <= csr_op(mtvec_q, rs1_data_i, csr_op_i);
                    MSCRATCH_ADDR: mscratch_q <= csr_op(mscratch_q, rs1_data_i, csr_op_i);
                    MEPC_ADDR:     mepc_q     <= csr_op(mepc_q, rs1_data_i, csr_op_i);
                    MCAUSE_ADDR:   mcause_q   <= csr_op(mcause_q, rs1_data_i, csr_op_i);
                    MTVAL_ADDR:    mtval_q    <= csr_op(mtval_q, rs1_data_i, csr_op_i);
                    MIP_ADDR:      mip_q      <= csr_op(mip_q, rs1_data_i, csr_op_i);
                    default: ;
                endcase
            end
        end
    end

    function automatic word_t csr_op(input word_t csr_val, input word_t write_val, input logic [2:0] op);
        case (op)
            CSR_OP_RW: return write_val;
            CSR_OP_RS: return csr_val | write_val;
            CSR_OP_RC: return csr_val & ~write_val;
            default:   return csr_val;
        endcase
    endfunction

    assign mepc_o    = mepc_q;
    assign mtvec_o   = mtvec_q;
    assign mstatus_o = mstatus_q;
    assign mie_o      = mie_q;
    assign mip_o      = mip_q;
    assign mcause_o   = mcause_q;
    assign mtval_o    = mtval_q;
    assign mstatus_mie_o = mstatus_q[3];
    assign mtvec_mode_o = mtvec_q[1:0];
    assign mtvec_base_o = mtvec_q[31:2];

endmodule
```

### 2.6. Exception Handler (`exception_handler.sv`)
- **Purpose**: Centralized module for detecting, prioritizing, and handling exceptions and interrupts.
- **Key Features**:
    - Receives exception information from various pipeline stages.
    - Resolves priorities among concurrent exceptions/interrupts.
    - Generates the trap vector address.
    - Coordinates with the CSR file for context saving (`mepc`, `mcause`, `mtval`).
    - Manages pipeline flush and PC redirection on trap.
- **Interface**: Inputs for exception info from stages, interrupt signals; outputs for valid exception, trap vector, and pipeline control signals.
- **Integration**: Receives inputs from Fetch, Decode, Execute, and Memory stages; controls PC in Fetch stage.

#### 2.6.1. Exception Handler Implementation Details
The `exception_handler` module is responsible for managing all exceptions and interrupts in the system. It receives exception information from various pipeline stages and interrupt signals, prioritizes them, and generates the appropriate trap vector address based on the `mtvec` CSR. It also handles QoS-enhanced memory access for exception handling and debug requests.

```systemverilog
module exception_handler #(
    parameter integer CORE_ID = 0
)(
    input  logic        clk_i,
    input  logic        rst_ni,
    input  exception_info_t fetch_exception_i,
    input  exception_info_t execute_exception_i,
    input  exception_info_t memory_exception_i,
    input  exception_info_t writeback_exception_i,
    input  logic        m_software_interrupt_i,
    input  logic        m_timer_interrupt_i,
    input  logic        m_external_interrupt_i,
    input  logic        mstatus_mie_i,
    input  logic        mie_msie_i,
    input  logic        mie_mtie_i,
    input  logic        mie_meie_i,
    input  logic        mip_msip_i,
    input  logic        mip_mtip_i,
    input  logic        mip_meip_i,
    input  addr_t       mtvec_base_i,
    input  logic [1:0]  mtvec_mode_i,
    output logic        exception_valid_o,
    output exception_info_t exception_info_o,
    output addr_t       trap_vector_o,
    output logic        pipeline_flush_o,
    output exception_info_t exception_o,
    output interrupt_info_t interrupt_info_o,
    output logic                mem_req_valid_o,
    output memory_req_t         mem_req_o,
    output qos_config_t         mem_qos_config_o,
    input  logic                mem_req_ready_i,
    input  logic                mem_rsp_valid_i,
    input  memory_rsp_t         mem_rsp_i,
    output logic                mem_rsp_ready_o,
    input  logic                debug_req_i,
    input  logic [31:0]         debug_addr_i,
    input  logic                debug_write_i,
    input  word_t               debug_wdata_i,
    output logic                debug_req_ready_o,
    output logic                debug_rsp_valid_o,
    output word_t               debug_rdata_o,
    output logic                debug_error_o,
    input  logic                qos_enable_i,
    output logic [31:0]         qos_violations_o
);

    exception_info_t fetch_exception_detected;
    exception_info_t execute_exception_detected;
    exception_info_t memory_exception_detected;
    exception_info_t writeback_exception_detected;
    exception_info_t interrupt_detected;
    exception_info_t selected_exception;
    logic [3:0] exception_priorities;
    logic [3:0] highest_priority;
    logic interrupt_enabled;

    assign interrupt_enabled = mstatus_mie_i;
    
    assign interrupt_info_o.m_software_interrupt = mip_msip_i && mie_msie_i && interrupt_enabled;
    assign interrupt_info_o.m_timer_interrupt = mip_mtip_i && mie_mtie_i && interrupt_enabled;
    assign interrupt_info_o.m_external_interrupt = mip_meip_i && mie_meie_i && interrupt_enabled;
    
    assign interrupt_info_o.interrupt_pending = interrupt_info_o.m_software_interrupt ||
                                               interrupt_info_o.m_timer_interrupt ||
                                               interrupt_info_o.m_external_interrupt;

    always_comb begin
        interrupt_info_o.interrupt_cause = EXC_CAUSE_M_SOFTWARE_INTERRUPT;
        if (interrupt_info_o.m_external_interrupt) begin
            interrupt_info_o.interrupt_cause = EXC_CAUSE_M_EXTERNAL_INTERRUPT;
        end else if (interrupt_info_o.m_timer_interrupt) begin
            interrupt_info_o.interrupt_cause = EXC_CAUSE_M_TIMER_INTERRUPT;
        end else if (interrupt_info_o.m_software_interrupt) begin
            interrupt_info_o.interrupt_cause = EXC_CAUSE_M_SOFTWARE_INTERRUPT;
        end
    end

    always_comb begin
        interrupt_detected.valid = interrupt_info_o.interrupt_pending;
        interrupt_detected.exc_type = EXC_TYPE_INTERRUPT;
        interrupt_detected.cause = interrupt_info_o.interrupt_cause;
        interrupt_detected.pc = '0;
        interrupt_detected.tval = '0;
        interrupt_detected.priority = PRIO_INTERRUPT;
    end

    assign fetch_exception_detected = fetch_exception_i;
    assign execute_exception_detected = execute_exception_i;
    assign memory_exception_detected = memory_exception_i;
    assign writeback_exception_detected = writeback_exception_i;

    assign exception_priorities[0] = fetch_exception_detected.valid ? fetch_exception_detected.priority : PRIO_NONE;
    assign exception_priorities[1] = execute_exception_detected.valid ? execute_exception_detected.priority : PRIO_NONE;
    assign exception_priorities[2] = memory_exception_detected.valid ? memory_exception_detected.priority : PRIO_NONE;
    assign exception_priorities[3] = writeback_exception_detected.valid ? writeback_exception_detected.priority : PRIO_NONE;

    always_comb begin
        highest_priority = PRIO_NONE;
        if (exception_priorities[0] != PRIO_NONE && exception_priorities[0] < highest_priority) highest_priority = exception_priorities[0];
        if (exception_priorities[1] != PRIO_NONE && exception_priorities[1] < highest_priority) highest_priority = exception_priorities[1];
        if (exception_priorities[2] != PRIO_NONE && exception_priorities[2] < highest_priority) highest_priority = exception_priorities[2];
        if (exception_priorities[3] != PRIO_NONE && exception_priorities[3] < highest_priority) highest_priority = exception_priorities[3];
    end

    always_comb begin
        selected_exception = '0;
        
        if (interrupt_detected.valid) begin
            selected_exception = interrupt_detected;
        end
        else if (fetch_exception_detected.valid && fetch_exception_detected.priority == highest_priority) begin
            selected_exception = fetch_exception_detected;
        end
        else if (execute_exception_detected.valid && execute_exception_detected.priority == highest_priority) begin
            selected_exception = execute_exception_detected;
        end
        else if (memory_exception_detected.valid && memory_exception_detected.priority == highest_priority) begin
            selected_exception = memory_exception_detected;
        end
        else if (writeback_exception_detected.valid && writeback_exception_detected.priority == highest_priority) begin
            selected_exception = writeback_exception_detected;
        end
    end

    always_comb begin
        if (selected_exception.valid) begin
            if (selected_exception.exc_type == EXC_TYPE_INTERRUPT) begin
                if (mtvec_mode_i == 2'b01) begin
                    trap_vector_o = {mtvec_base_i[31:2], 2'b00} + (selected_exception.cause << 2);
                end else begin
                    trap_vector_o = {mtvec_base_i[31:2], 2'b00};
                end
            end else begin
                if (mtvec_mode_i == 2'b01) begin
                    trap_vector_o = {mtvec_base_i[31:2], 2'b00} + (selected_exception.cause << 2);
                end else begin
                    trap_vector_o = {mtvec_base_i[31:2], 2'b00};
                end
            end
        end else begin
            trap_vector_o = '0;
        end
    end

    assign exception_valid_o = selected_exception.valid;
    assign exception_info_o = selected_exception;
    assign exception_o = selected_exception;
    assign pipeline_flush_o = selected_exception.valid;

    function automatic qos_config_t get_exception_qos_config(
        input exception_info_t exc_info,
        input logic is_debug,
        input logic is_interrupt
    );
        qos_config_t qos_config;
        
        qos_config.urgent = 1'b1;
        qos_config.guaranteed_bw = 1'b1;
        qos_config.weight = QOS_WEIGHT_CRITICAL;
        qos_config.bandwidth_percent = QOS_EXCEPTION_BW_PERCENT;
        qos_config.preemptable = 1'b0;
        qos_config.real_time = 1'b1;
        qos_config.retry_limit = QOS_EXCEPTION_RETRY_LIMIT;
        qos_config.ordered = 1'b1;
        qos_config.core_id = CORE_ID[3:0];
        
        if (is_debug) begin
            qos_config.qos_level = QOS_LEVEL_CRITICAL;
            qos_config.transaction_type = QOS_TYPE_DEBUG;
            qos_config.max_latency_cycles = 16'd5;
        end else if (is_interrupt) begin
            qos_config.qos_level = QOS_LEVEL_CRITICAL;
            qos_config.transaction_type = QOS_TYPE_EXCEPTION;
            qos_config.max_latency_cycles = 16'd10;
        end else begin
            case (exc_info.cause)
                EXC_CAUSE_INSTR_ACCESS_FAULT,
                EXC_CAUSE_LOAD_ACCESS_FAULT,
                EXC_CAUSE_STORE_ACCESS_FAULT: begin
                    qos_config.qos_level = QOS_LEVEL_CRITICAL;
                    qos_config.transaction_type = QOS_TYPE_EXCEPTION;
                    qos_config.max_latency_cycles = 16'd10;
                end
                
                EXC_CAUSE_BREAKPOINT: begin
                    qos_config.qos_level = QOS_LEVEL_CRITICAL;
                    qos_config.transaction_type = QOS_TYPE_DEBUG;
                    qos_config.max_latency_cycles = 16'd5;
                end
                
                EXC_CAUSE_ECALL_M: begin
                    qos_config.qos_level = QOS_LEVEL_HIGH;
                    qos_config.transaction_type = QOS_TYPE_EXCEPTION;
                    qos_config.max_latency_cycles = 16'd15;
                end
                
                default: begin
                    qos_config.qos_level = QOS_LEVEL_HIGH;
                    qos_config.transaction_type = QOS_TYPE_EXCEPTION;
                    qos_config.max_latency_cycles = 16'd20;
                end
            endcase
        end
        
        return qos_config;
    endfunction

    logic exception_memory_access_needed;
    logic debug_memory_access_needed;
    logic [31:0] qos_violation_counter;
    qos_config_t exception_qos_config;
    qos_config_t debug_qos_config;
    
    always_comb begin : proc_exception_memory_qos
        exception_memory_access_needed = selected_exception.valid && (
            (mtvec_mode_i == 2'b01) ||
            (selected_exception.cause == EXC_CAUSE_LOAD_ACCESS_FAULT) ||
            (selected_exception.cause == EXC_CAUSE_STORE_ACCESS_FAULT) ||
            (selected_exception.cause == EXC_CAUSE_INSTR_ACCESS_FAULT)
        );
        
        exception_qos_config = get_exception_qos_config(
            selected_exception,
            1'b0,
            interrupt_detected.valid
        );
        
        debug_memory_access_needed = debug_req_i;
        debug_qos_config = get_exception_qos_config(
            '0,
            1'b1,
            1'b0
        );
    end

    always_comb begin : proc_qos_memory_arbitration
        mem_req_valid_o = 1'b0;
        mem_req_o = '0;
        mem_qos_config_o = '0;
        debug_req_ready_o = 1'b0;
        
        if (debug_memory_access_needed && qos_enable_i) begin
            mem_req_valid_o = 1'b1;
            mem_req_o.addr = debug_addr_i;
            mem_req_o.write = debug_write_i;
            mem_req_o.data = debug_wdata_i;
            mem_req_o.strb = 4'hF;
            mem_qos_config_o = debug_qos_config;
            debug_req_ready_o = mem_req_ready_i;
        end else if (exception_memory_access_needed && qos_enable_i) begin
            mem_req_valid_o = 1'b1;
            
            if (mtvec_mode_i == 2'b01) begin
                mem_req_o.addr = {mtvec_base_i[31:2], 2'b00} + (selected_exception.cause << 2);
            end else begin
                mem_req_o.addr = {mtvec_base_i[31:2], 2'b00};
            end
            
            mem_req_o.write = 1'b0;
            mem_req_o.data = '0;
            mem_req_o.strb = 4'hF;
            mem_qos_config_o = exception_qos_config;
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_qos_monitoring
        if (!rst_ni) begin
            qos_violation_counter <= 0;
        end else begin
            if (mem_req_valid_o && !mem_req_ready_i) begin
                qos_violation_counter <= qos_violation_counter + 1;
            end
            
            if (debug_req_i && !debug_req_ready_o) begin
                qos_violation_counter <= qos_violation_counter + 1;
            end
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_debug_response
        if (!rst_ni) begin
            debug_rsp_valid_o <= 1'b0;
            debug_rdata_o <= '0;
            debug_error_o <= 1'b0;
        end else begin
            if (mem_rsp_valid_i && debug_memory_access_needed) begin
                debug_rsp_valid_o <= 1'b1;
                debug_rdata_o <= mem_rsp_i.data;
                debug_error_o <= mem_rsp_i.error;
            end else begin
                debug_rsp_valid_o <= 1'b0;
                debug_error_o <= 1'b0;
            end
        end
    end

    assign qos_violations_o = qos_violation_counter;
    assign mem_rsp_ready_o = 1'b1;

endmodule
```

### 2.7. QoS Exception Handler (`qos_exception_handler.sv`)
- **Purpose**: (If distinct from main exception handler) Likely handles Quality of Service (QoS) related exceptions or integrates QoS considerations into exception prioritization.
- **Note**: If this module is a part of or an extension to the main `exception_handler.sv`, its role should be clarified within the overall exception handling architecture.

#### 2.7.1. QoS Exception Handler Implementation Details

Upon reviewing `qos_exception_handler.sv`, it appears that its functionality, including QoS-enhanced exception handling and debug memory access, has been fully integrated into `exception_handler.sv`. Therefore, `qos_exception_handler.sv` is redundant and should be considered deprecated. The comprehensive exception and interrupt handling, along with QoS management for critical memory accesses, is now handled solely by `exception_handler.sv`.

## 3. Design Principles
- **Modularity**: Each unit is a self-contained module with clear interfaces.
- **Parameterization**: Units are parameterized to allow flexible configuration (e.g., data widths, number of entries).
- **Pipelining**: Multi-cycle units (Multiplier, Divider) are pipelined to maintain high throughput.
- **Hazard Awareness**: Designed to integrate with the pipeline's hazard detection and forwarding mechanisms.

## 4. Integration with Pipeline
These functional units are primarily integrated into the Execute stage, where instructions are performed. The Decode stage provides the necessary operands and control signals, and the Writeback stage receives the results for writing back to the Register File.

## 5. Future Enhancements
- **Floating Point Unit (FPU)**: Dedicated hardware for floating-point arithmetic (already present as `fpu_unit.sv` in `rtl/core/`).
- **Vector Processing Unit (VPU)**: Hardware for vector operations (already present as `vpu_unit.sv` in `rtl/core/`).
- **Machine Learning Inference Unit (MLIU)**: Hardware for ML inference (already present as `ml_inference_unit.sv` in `rtl/core/`).
- **Advanced Multi-cycle Units**: Further optimization of multi-cycle units for higher performance.
- **Custom Functional Units**: Support for user-defined custom instructions.
