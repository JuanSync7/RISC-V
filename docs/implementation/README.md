# Implementation Documentation

This directory contains key technical documents that provide a detailed view of the final RISC-V processor implementation. While most high-level summaries have been moved to the `consolidated/` directory, these files offer deep dives into specific, critical aspects of the design.

## Core Documents

-   **[CURRENT_IMPLEMENTATION.md](./CURRENT_IMPLEMENTATION.md)**  
    A comprehensive, low-level description of the final, current state of the RTL implementation. This document provides the most detailed view of the processor's architecture and is considered the primary technical reference.

-   **[RTL_MODULE_CREATION_GUIDE.md](./RTL_MODULE_CREATION_GUIDE.md)**  
    A valuable development guide that outlines the standards, styles, and procedures for creating new RTL modules within this project. It includes details on documentation (`AI_TAGS`), coding style, and parameterization.

-   **[EXCEPTION_HANDLING_IMPLEMENTATION.md](./EXCEPTION_HANDLING_IMPLEMENTATION.md)**  
    A specific and detailed technical document covering the implementation of the exception and interrupt handling system. It details the logic within `exception_handler.sv` and its interaction with the pipeline and CSRs.

-   **[MEMORY_WRAPPER_IMPLEMENTATION.md](./MEMORY_WRAPPER_IMPLEMENTATION.md)**  
    A focused document explaining the design and implementation of the `memory_wrapper.sv` module, which serves as the primary interface between the core's memory hierarchy and the external protocol adapters.