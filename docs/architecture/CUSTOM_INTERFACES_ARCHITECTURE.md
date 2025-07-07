# Custom Interfaces Architecture

## 1. Overview
This document describes the custom SystemVerilog interfaces used within the RISC-V core design. These interfaces are crucial for defining clear communication protocols between modules, enhancing modularity, reusability, and verification efficiency. They encapsulate related signals, making connections cleaner and less error-prone.

## 2. Key Principles of Interface Usage
- **Encapsulation**: Grouping related signals (e.g., address, data, valid, ready) into a single interface.
- **Modports**: Defining distinct views (e.g., Master, Slave, Monitor) for each side of a connection, ensuring correct signal directionality.
- **Reusability**: Interfaces can be easily reused across different modules and projects.
- **Verification Friendly**: Simplifies testbench development by providing a clear, transaction-level view of communication.

## 3. Interfaces in the Design

### 3.1. AXI4 Interface (`axi4_if.sv`)
- **Purpose**: Defines the ARM AMBA AXI4 protocol for high-performance, high-bandwidth communication with external memory and peripherals.
- **Key Signals and Protocol**: AXI4 is a channel-based protocol with separate channels for read address, read data, write address, write data, and write response. Each channel uses a `VALID`/`READY` handshake mechanism.
    -   **Write Address Channel (AW)**: `AWVALID`, `AWREADY`, `AWADDR`, `AWLEN`, `AWSIZE`, `AWBURST`, `AWLOCK`, `AWCACHE`, `AWPROT`, `AWQOS`, `AWREGION`, `AWUSER`, `AWID`.
        -   `AWVALID`/`AWREADY`: Handshake for address transfer.
        -   `AWADDR`: Start address of the write burst.
        -   `AWLEN`: Length of the burst (number of transfers).
        -   `AWID`: Transaction ID for out-of-order completion.
    -   **Write Data Channel (W)**: `WVALID`, `WREADY`, `WDATA`, `WSTRB`, `WLAST`, `WUSER`.
        -   `WVALID`/`WREADY`: Handshake for data transfer.
        -   `WDATA`: Write data payload.
        -   `WSTRB`: Byte strobes, indicating valid bytes within `WDATA`.
        -   `WLAST`: Indicates the last transfer in a write burst.
    -   **Write Response Channel (B)**: `BVALID`, `BREADY`, `BRESP`, `BID`, `BUSER`.
        -   `BVALID`/`BREADY`: Handshake for write response.
        -   `BRESP`: Write response status (e.g., OKAY, EXOKAY, SLVERR, DECERR).
        -   `BID`: Transaction ID matching the `AWID`.
    -   **Read Address Channel (AR)**: `ARVALID`, `ARREADY`, `ARADDR`, `ARLEN`, `ARSIZE`, `ARBURST`, `ARLOCK`, `ARCACHE`, `ARPROT`, `ARQOS`, `ARREGION`, `ARUSER`, `ARID`.
        -   `ARVALID`/`ARREADY`: Handshake for address transfer.
        -   `ARADDR`: Start address of the read burst.
        -   `ARLEN`: Length of the burst.
        -   `ARID`: Transaction ID.
    -   **Read Data Channel (R)**: `RVALID`, `RREADY`, `RDATA`, `RRESP`, `RLAST`, `RUSER`, `RID`.
        -   `RVALID`/`RREADY`: Handshake for data transfer.
        -   `RDATA`: Read data payload.
        -   `RRESP`: Read response status.
        -   `RLAST`: Indicates the last transfer in a read burst.
        -   `RID`: Transaction ID matching the `ARID`.
- **Timing Diagram (Conceptual Handshake)**:

```
Clock: __/\__/\__/\__/\__/\__/\__/\__/\__
VALID: ____/\____________
READY: ______/\__________
Data:  ───────<==========>───
```

- **Modports**: Includes `master` (initiates transactions), `slave` (responds to transactions), and `monitor` (observes all transactions) modports.

### 3.2. Cache Coherency Interface (`cache_coherency_if.sv`)
- **Purpose**: Defines the signals and protocol for maintaining cache coherency between multiple RISC-V cores and the memory hierarchy, based on a MESI-like protocol.
- **Key Signals and Protocol**: This interface facilitates requests from L1 caches to a central coherency manager (e.g., in L2) and snoop requests from the manager to L1s.
    -   **Request from L1 to Manager**: `req_valid`, `req_ready`, `req_addr`, `req_type`, `req_source`.
        -   `req_valid`/`req_ready`: Handshake for coherency request.
        -   `req_addr`: Address of the cache line.
        -   `req_type`: Type of coherency request (e.g., ReadShared, ReadExclusive, WriteBack).
        -   `req_source`: ID of the requesting core.
    -   **Response from Manager to L1**: `rsp_valid`, `rsp_ready`, `rsp_state`, `rsp_data`.
        -   `rsp_valid`/`rsp_ready`: Handshake for coherency response.
        -   `rsp_state`: New state of the cache line (e.g., Modified, Exclusive, Shared, Invalid).
        -   `rsp_data`: Data associated with the response (e.g., for a cache fill).
    -   **Snoop Request from Manager to L1**: `snoop_valid`, `snoop_ready`, `snoop_addr`, `snoop_type`.
        -   `snoop_valid`/`snoop_ready`: Handshake for snoop request.
        -   `snoop_addr`: Address of the cache line to snoop.
        -   `snoop_type`: Type of snoop (e.g., SnoopRead, SnoopWrite).
    -   **Snoop Response from L1 to Manager**: `snoop_rsp_valid`, `snoop_rsp_data_en`, `snoop_rsp_data`.
        -   `snoop_rsp_valid`: Indicates a valid snoop response.
        -   `snoop_rsp_data_en`: Indicates if data is included in the response.
        -   `snoop_rsp_data`: Data from the snooped cache line.
- **Modports**: Includes `l1_cache_port` (for L1 caches) and `coherency_controller_port` (for the central manager).

### 3.3. CHI Interface (`chi_if.sv`)
- **Purpose**: Defines the ARM Coherent Hub Interface (CHI) protocol, a more advanced cache-coherent interconnect for multi-core systems.
- **Key Signals and Protocol**: CHI uses a flit-based (flow control unit) protocol across multiple channels (Request, Response, Data, Snoop).
    -   **Request Channel (REQ)**: `req_addr`, `req_opcode`, `req_size`, `req_srcid`, `req_txnid`, `req_tgtid`, `reqflitv`, `reqlcrdv`.
        -   `req_opcode`: Defines the type of request (e.g., ReadNoSnp, WriteNoSnpFull, ReadShared).
        -   `req_txnid`: Transaction ID.
        -   `reqflitv`/`reqlcrdv`: Flit valid/link credit ready handshake.
    -   **Response Channel (RSP)**: `rsp_opcode`, `rsp_resperr`, `rsp_txnid`, `rspflitv`, `rsplcrdv`.
        -   `rsp_opcode`: Defines the type of response (e.g., CompAck, RespSepData).
        -   `rsp_resperr`: Response error status.
        -   `rspflitv`/`rsplcrdv`: Flit valid/link credit ready handshake.
    -   **Data Channel (DAT)**: `dat_opcode`, `dat_data`, `dat_txnid`, `datflitv`, `datlcrdv`.
        -   `dat_opcode`: Defines the type of data transfer (e.g., NonCopyBackWrData, ReadData).
        -   `dat_data`: Data payload.
        -   `datflitv`/`datlcrdv`: Flit valid/link credit ready handshake.
    -   **Snoop Channel (SNP)**: `snp_addr`, `snp_opcode`, `snp_txnid`, `snpflitv`, `snplcrdv`.
        -   `snp_opcode`: Defines the type of snoop request (e.g., SnpOnce, SnpUnique).
        -   `snpflitv`/`snplcrdv`: Flit valid/link credit ready handshake.
- **Modports**: Includes `rn` (Request Node, typically a core), `hn` (Home Node, typically a memory controller or interconnect), and `monitor`.

### 3.4. Inter-Core Communication Interface (`inter_core_comm_if.sv`)
- **Purpose**: Defines a point-to-point-like network for direct message passing and interrupt signaling between multiple cores and a central Core Manager.
- **Key Signals and Protocol**: Each core has dedicated send and receive channels to/from the manager.
    -   **Core to Manager (Send)**: `send_valid_w`, `send_ready_w`, `send_dest_id_w`, `send_message_w`.
        -   `send_valid_w`/`send_ready_w`: Handshake for sending a message from a core.
        -   `send_dest_id_w`: Target core ID.
        -   `send_message_w`: Message payload.
    -   **Manager to Core (Receive)**: `recv_valid_w`, `recv_ready_w`, `recv_source_id_w`, `recv_message_w`.
        -   `recv_valid_w`/`recv_ready_w`: Handshake for receiving a message at a core.
        -   `recv_source_id_w`: Source core ID.
        -   `recv_message_w`: Received message payload.
    -   **QoS Enhancements**: Includes `msg_qos_config`, `urgent_msg`, `guaranteed_delivery`, `msg_type` for Quality of Service management of inter-core messages.
- **Modports**: Includes `core` (for individual core instances) and `manager` (for the central Core Manager).

### 3.5. Memory Request/Response Interface (`memory_req_rsp_if.sv`)
- **Purpose**: Defines a generic, protocol-agnostic request/response protocol for memory accesses. This interface abstracts the underlying bus protocol, allowing core components to interact with memory without direct knowledge of AXI, CHI, or TileLink.
- **Key Signals and Protocol**: A simple `VALID`/`READY` handshake for requests and responses.
    -   **Request**: `req_valid`, `req_ready`, `req.addr`, `req.write`, `req.size`, `req.data`, `req.strb`, `req.id`, `req.prot`, `req.cacheable`.
        -   `req_valid`/`req_ready`: Handshake for memory request.
        -   `req.addr`: Memory address.
        -   `req.write`: Indicates a write operation (else read).
        -   `req.size`: Size of the access (byte, half-word, word).
        -   `req.data`: Write data for store operations.
        -   `req.strb`: Byte strobes for partial writes.
        -   `req.id`: Transaction ID.
    -   **Response**: `rsp_valid`, `rsp_ready`, `rsp.data`, `rsp.id`, `rsp.error`, `rsp.last`.
        -   `rsp_valid`/`rsp_ready`: Handshake for memory response.
        -   `rsp.data`: Read data for load operations.
        -   `rsp.id`: Transaction ID matching the request.
        -   `rsp.error`: Indicates a memory access error.
- **Modports**: Includes `master` (initiates requests) and `slave` (responds to requests).

### 3.6. Synchronization Primitives Interface (`sync_primitives_if.sv`)
- **Purpose**: Defines the interface for hardware synchronization primitives, primarily hardware barriers, allowing multiple cores to synchronize their execution.
- **Key Signals and Protocol**: Uses `VALID`/`READY` handshakes for core arrival and release from a barrier.
    -   **Core to Manager (Arrival)**: `arrive_valid_w`, `arrive_ready_w`, `barrier_id_w`.
        -   `arrive_valid_w`/`arrive_ready_w`: Handshake for a core signaling its arrival at a barrier.
        -   `barrier_id_w`: ID of the barrier.
    -   **Manager to Core (Release)**: `release_valid_w`, `release_ready_w`.
        -   `release_valid_w`/`release_ready_w`: Handshake for the manager releasing a core from a barrier.
- **Modports**: Includes `manager` (for the central synchronization manager).

### 3.7. TileLink Interface (`tilelink_if.sv`)
- **Purpose**: Defines the SiFive TileLink protocol, a simple, scalable, and open-source interconnect protocol, supporting both Uncached (TL-UL) and Cached (TL-C) operations.
- **Key Signals and Protocol**: TileLink uses a channel-based protocol (Channel A for requests, Channel D for responses) with `VALID`/`READY` handshakes.
    -   **Channel A (Requests)**: `a_valid`, `a_ready`, `a_opcode`, `a_param`, `a_size`, `a_source`, `a_address`, `a_mask`, `a_data`, `a_corrupt`.
        -   `a_opcode`: Type of request (e.g., `Get`, `PutFullData`, `PutPartialData`).
        -   `a_size`: Log2 of the transfer size in bytes.
        -   `a_source`: Source ID for transaction tracking.
        -   `a_address`: Target address.
        -   `a_data`: Write data for Put operations.
    -   **Channel D (Responses)**: `d_valid`, `d_ready`, `d_opcode`, `d_param`, `d_size`, `d_source`, `d_sink`, `d_denied`, `d_data`, `d_corrupt`.
        -   `d_opcode`: Type of response (e.g., `AccessAck`, `AccessAckData`).
        -   `d_source`: Echoes the `a_source` of the corresponding request.
        -   `d_data`: Read data for Get responses.
        -   `d_denied`: Indicates if the request was denied.
- **Modports**: Includes `master` (initiates transactions, also called `client`), `slave` (responds to transactions, also called `manager`), and `monitor`.

## 4. Usage Guidelines
- **Instantiation**: Always instantiate interfaces by name, connecting them to modules using named port connections.
- **Modport Usage**: Always specify the correct modport when connecting an interface to a module to ensure proper signal directionality.
- **Parameterization**: Interfaces can be parameterized (e.g., data width, address width) to enhance reusability.

## 5. Future Enhancements
- **Formal Verification of Interfaces**: Use formal methods to verify protocol compliance and deadlock freedom.
- **Interface Adapters**: Develop generic adapters to convert between different interface types.
- **Transaction-Level Modeling (TLM)**: Explore TLM for higher-level modeling and verification of interface interactions.