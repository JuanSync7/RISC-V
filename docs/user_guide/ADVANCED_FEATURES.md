# RISC-V Core Advanced Features

This document provides an overview of the advanced features available in the RISC-V core. These features are designed to enhance performance, improve efficiency, and provide greater flexibility for complex applications.

## Table of Contents

- [Introduction](#introduction)
- [Out-of-Order Execution](#out-of-order-execution)
- [Advanced Branch Prediction](#advanced-branch-prediction)
- [Multi-level Cache Hierarchy](#multi-level-cache-hierarchy)
- [Quality of Service (QoS)](#quality-of-service-qos)
- [Multi-Core System](#multi-core-system)

## Introduction

The RISC-V core is more than just a simple in-order pipeline. It incorporates several advanced micro-architectural features that are typically found in high-performance processors. This guide provides a high-level overview of these features and points you to the relevant source files for more detailed information.

## Out-of-Order Execution

To maximize instruction throughput, the core supports out-of-order (OoO) execution. This allows the processor to execute instructions as soon as their operands are ready, rather than being stalled by a preceding instruction that is waiting for data.

Key components of the OoO engine include:

-   **Re-order Buffer (ROB)**: Buffers instructions and allows them to commit in program order. See `rtl/core/execution/reorder_buffer.sv`.
-   **Reservation Stations (RS)**: Hold instructions waiting for their operands to become available. See `rtl/core/execution/reservation_station.sv`.
-   **Register Renaming**: Eliminates false data dependencies (WAW, WAR) by mapping architectural registers to a larger set of physical registers. See `rtl/core/execution/register_renaming.sv`.

## Advanced Branch Prediction

The core implements a sophisticated branch prediction unit to minimize the performance penalty of control hazards.

-   **Tournament Predictor**: This predictor uses a combination of a local history-based predictor and a global history-based predictor, with a meta-predictor to choose between them. This provides high accuracy across different types of branch behavior. See `rtl/core/prediction/tournament_predictor.sv`.
-   **Branch Target Buffer (BTB)**: Caches the target addresses of recently taken branches.
-   **Return Address Stack (RAS)**: Predicts return addresses for function calls. See `rtl/core/prediction/return_stack_buffer.sv`.

## Multi-level Cache Hierarchy

The memory subsystem features a multi-level cache hierarchy to reduce memory latency.

-   **L1 Caches**: Separate instruction and data caches for low-latency access. See `rtl/memory/cache/icache.sv`.
-   **L2 Cache**: A unified L2 cache that serves as a backstop for the L1 caches. See `rtl/memory/cache/l2_cache.sv`.
-   **L3 Cache**: An optional large L3 cache for high-end systems. See `rtl/memory/cache/l3_cache.sv`.
-   **Cache Coherency**: The system includes a cache coherency controller to ensure data consistency in multi-core configurations. See `rtl/memory/coherency/cache_coherency_controller.sv`.

## Quality of Service (QoS)

The core integrates a Quality of Service (QoS) mechanism to manage resources and prioritize memory accesses. This is critical for real-time systems and applications with diverse performance requirements.

-   **QoS Arbiter**: Prioritizes memory requests based on their assigned QoS level. See `rtl/protocol/custom/qos_arbiter.sv`.
-   **CSR Registers**: The QoS parameters can be configured through dedicated CSRs. See `rtl/core/qos_csr_regfile.sv`.

## Multi-Core System

The architecture is designed to be scalable to a multi-core system, enabling higher overall performance through parallel processing.

-   **Core Manager**: Manages the lifecycle and communication of multiple cores. See `rtl/core/integration/core_manager.sv`.
-   **Inter-Core Communication**: The system provides interfaces for communication and synchronization between cores. See `rtl/shared/interfaces/inter_core_comm_if.sv`. 