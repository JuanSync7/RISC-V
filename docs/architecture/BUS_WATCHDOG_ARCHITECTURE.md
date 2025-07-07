# Bus Watchdog Architecture

## 1. Overview

The `bus_watchdog` module implements a simple watchdog timer designed to detect bus timeouts within the RISC-V system. It monitors a specific enable signal and, if active for a configurable number of clock cycles, asserts a timeout signal. This mechanism is crucial for system reliability, preventing indefinite hangs due to unresponsive bus transactions.

## 2. Features

- **Configurable Timeout**: The timeout duration can be set via a parameter.
- **Bus Activity Monitoring**: Detects prolonged bus inactivity or stalled transactions.
- **Timeout Assertion**: Provides a clear output signal when a timeout occurs.
- **Asynchronous Reset**: Supports asynchronous reset for robust operation.

## 3. Internal Blocks

The `bus_watchdog` module primarily consists of a single internal counter:

- **`counter_q`**:
    - **Description**: An internal register that increments on each clock cycle when the `enable_i` signal is asserted. It resets when `enable_i` is deasserted or when the timeout limit is reached.
    - **Functionality**: Tracks the elapsed time (in clock cycles) since the `enable_i` signal became active.

## 4. Interfaces and Ports

| Port Name        | Direction | Width (bits) | Description                                      |
| :--------------- | :-------- | :----------- | :----------------------------------------------- |
| `clk_i`          | Input     | 1            | System clock.                                    |
| `rst_ni`         | Input     | 1            | Asynchronous reset (active low).                 |
| `enable_i`       | Input     | 1            | Enables the watchdog timer when high.            |
| `timeout_o`      | Output    | 1            | Asserted when the timeout duration is reached.   |

## 5. Parameters

| Parameter Name   | Type      | Default Value | Description                                      |
| :--------------- | :-------- | :------------ | :----------------------------------------------- |
| `TIMEOUT_CYCLES` | `integer` | `1000`        | The number of clock cycles after which a timeout is asserted if `enable_i` remains high. |

## 6. Design Details

The `bus_watchdog` operates by continuously incrementing an internal counter (`counter_q`) when the `enable_i` signal is high. If `enable_i` goes low, the counter is reset to zero. When the counter reaches `TIMEOUT_CYCLES - 1`, the `timeout_o` signal is asserted, indicating that the bus transaction has exceeded its allowed time. The counter also resets to zero upon reaching the timeout limit, allowing for continuous monitoring.

## 7. Verification and Testing

Verification of the `bus_watchdog` module typically involves:
- **Unit Testing**: Testing the counter's behavior, ensuring it increments correctly, resets on `rst_ni` and `enable_i` deassertion, and asserts `timeout_o` at the correct cycle.
- **Timeout Scenarios**: Simulating scenarios where `enable_i` remains high for longer than `TIMEOUT_CYCLES` to confirm `timeout_o` assertion.
- **Reset Scenarios**: Verifying proper reset behavior under various conditions.

## 8. Future Enhancements

- **Programmable Timeout**: Allow `TIMEOUT_CYCLES` to be configured via a register during runtime.
- **Interrupt Generation**: Add an interrupt output to signal the CPU upon timeout.
- **Multiple Watchdogs**: Support for multiple independent watchdog instances for different bus interfaces.
