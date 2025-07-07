# Protocol Abstraction Architecture

## 1. Overview
This document describes the architecture of the protocol abstraction layer within the RISC-V memory subsystem. This layer enables the core to communicate with various external interconnect protocols (AXI4, CHI, TileLink) through a unified, protocol-agnostic internal interface. It also supports dynamic protocol switching and Quality of Service (QoS) management.

## 2. Key Features
- **Multi-Protocol Support**: Adapters for AXI4, CHI, and TileLink protocols.
- **Dynamic Protocol Switching**: Runtime selection of the active protocol based on configuration or workload.
- **Protocol-Agnostic Internal Interface**: A standardized internal memory request/response interface for the core.
- **Quality of Service (QoS) Management**: Priority-based arbitration and bandwidth control across different protocols.
- **Performance Monitoring**: Tracks protocol-specific metrics like latency and bandwidth.

## 3. Core Components

### 3.1. Protocol Factory (`protocol_factory.sv`)
- **Purpose**: The central module responsible for dynamic protocol switching and routing memory requests to the currently selected protocol adapter.
- **Functionality**:
    - Instantiates and connects all individual protocol adapters.
    - Selects the active protocol based on a configuration register or intelligent logic.
    - Multiplexes the internal memory interface requests to the chosen adapter.
    - Demultiplexes responses from the adapters back to the internal memory interface.
    - Collects performance metrics from the active protocol.

### 3.2. Protocol Adapters
Each supported protocol has a dedicated adapter module responsible for translating between the internal protocol-agnostic memory interface and the specific external protocol.

#### 3.2.1. AXI4 Adapter (`axi4_adapter.sv`)
- **Purpose**: Translates internal memory requests/responses to/from the ARM AMBA AXI4 protocol.
- **Features**: Full AXI4 compliance, burst support, configurable data/address/ID widths.

#### 3.2.2. CHI Adapter (`chi_adapter.sv`)
- **Purpose**: Translates internal memory requests/responses to/from the ARM Coherent Hub Interface (CHI) protocol.
- **Features**: Supports coherent cache operations, snoop transactions, and transaction tracking.

#### 3.2.3. TileLink Adapter (`tilelink_adapter.sv`)
- **Purpose**: Translates internal memory requests/responses to/from the SiFive TileLink protocol (TL-UL and TL-C).
- **Features**: Lightweight transaction overhead, support for various transfer sizes, and transaction ID tracking.

### 3.3. QoS Arbiter (`qos_arbiter.sv`)
- **Purpose**: Manages Quality of Service (QoS) for memory transactions, ensuring that high-priority requests receive preferential treatment and preventing starvation.
- **Functionality**:
    - Implements priority-based arbitration with anti-starvation mechanisms.
    - Supports configurable QoS levels and arbitration modes.
    - Tracks QoS violations and starvation flags.

## 4. Protocol Switching Mechanism

- **Configuration Register**: The `protocol_factory` receives a configuration input (`config_reg_i`) that determines the currently active protocol.
- **Pipelined Multiplexer**: The `protocol_factory` uses a pipelined multiplexer to route requests to the selected adapter and responses back, optimizing for high frequency.
- **Dynamic Selection (Future)**: The architecture supports future enhancements for AI-driven or workload-aware dynamic protocol selection.

## 5. QoS Management

- **QoS Level Assignment**: Each memory request is assigned a QoS level (e.g., based on transaction type, address range).
- **Arbiter Function**: The `qos_arbiter` uses these QoS levels to prioritize requests, ensuring critical transactions meet their latency and bandwidth requirements.

## 6. Integration with System

- **Memory Subsystem**: The protocol abstraction layer sits between the core's memory stage (or caches) and the external interconnect.
- **Core**: The core interacts with the memory system through the generic `memory_req_rsp_if`.
- **External Interconnect**: The protocol adapters connect to the physical pins of the chip, implementing the chosen external protocol.

## 7. Directory Structure (`rtl/protocol/`)

```
protocol/
├── axi/                    # AXI4 specific modules (e.g., axi4_adapter.sv)
├── chi/                    # CHI specific modules (e.g., chi_adapter.sv)
├── tilelink/               # TileLink specific modules (e.g., tilelink_adapter.sv)
├── custom/                 # Custom protocol implementations (e.g., protocol_factory.sv, qos_arbiter.sv)
└── README.md               # This file
```

## 8. Future Enhancements
- **New Protocol Support**: Addition of adapters for other industry-standard protocols (e.g., AXI5, CXL, NVLink, PCIe).
- **Advanced QoS**: More sophisticated QoS mechanisms with Service Level Agreement (SLA) enforcement.
- **Machine Learning-based Optimization**: AI-driven protocol selection and traffic management.
- **Protocol Compression/Encryption**: Support for secure and efficient data transfer.
