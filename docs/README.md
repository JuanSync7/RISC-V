# RISC-V Multi-Core System Documentation

**Project:** RISC-V RV32IM Multi-Core Processor  
**Status:** 🔄 **DEVELOPMENT IN PROGRESS**  
**Last Updated:** 2025-07-05  
**Documentation Version:** 2.0 (Reorganized)

---

## 🗂️ Documentation Structure

This documentation has been reorganized for optimal navigation and reduced redundancy. The new structure provides:

-   **Consolidated Reports:** Key topics are summarized in single, authoritative documents.
-   **Directory-Specific Guides:** Detailed READMEs for each major code directory.
-   **Clear Navigation:** A central point to access all project documentation.

---

## 📋 Primary Documents

### **🎯 Current Status & Overview**

-   **[CURRENT_PROJECT_STATUS.md](CURRENT_PROJECT_STATUS.md)** ⭐ **START HERE**
    -   The authoritative source for the current project status, performance metrics, and production readiness.

### **📁 Consolidated Topic Reports**

-   **[RTL Implementation Report](consolidated/RTL_IMPLEMENTATION_COMPLETE.md)**
    -   The complete and final reference for the RTL implementation, architecture, and performance.
-   **[Comprehensive Verification Report](consolidated/VERIFICATION_COMPREHENSIVE.md)**
    -   A summary of the verification strategy, coverage metrics, and final results.
-   **[QoS System Documentation](consolidated/QOS_SYSTEM_COMPLETE.md)**
    -   A complete guide to the Quality of Service (QoS) system, including its architecture and future roadmap.
-   **[Phase Completion Summary](consolidated/PHASE_COMPLETION_SUMMARY.md)**
    -   A high-level summary of the achievements from the project's major development phases.

---

## 🏗️ Architecture Documentation (`architecture/`)

This directory describes the high-level architecture of the processor.

-   **[Pipeline](./architecture/pipeline.md)**
-   **[Memory System](./architecture/memory_system.md)**
-   **[Performance](./architecture/performance.md)**
-   **[Exception Handling](./architecture/exception_handling.md)**

---

## 🔧 Implementation Documentation (`implementation/`)

This directory contains deep-dive technical documents for specific implementation details. See the [README](./implementation/README.md) for a full guide.

-   **[Current Implementation Details](./implementation/CURRENT_IMPLEMENTATION.md)**
-   **[RTL Module Creation Guide](./implementation/RTL_MODULE_CREATION_GUIDE.md)**

---

## 🧪 Verification Documentation (`verification/`)

This directory contains supplementary verification documents. See the [README](./verification/README.md) for a full guide.

-   **[Verification Plan](./verification/verification_plan.md)**
-   **[Testbench Structure](./verification/testbench_structure.md)**

---

## 📖 User Guide (`user_guide/`)

This directory contains documentation for users and integrators of the IP.

-   **[Getting Started](./user_guide/getting_started.md)**
-   **[Troubleshooting](./user_guide/troubleshooting.md)**

---

## 🗺️ Code Directory Guides

For detailed information on the RTL and testbench codebases, refer to the READMEs within those directories.

-   **[RTL Directory Guide](../rtl/README.md)**
-   **[Testbench Directory Guide](../tb/README.md)**
-   **[Scripts Directory Guide](../scripts/README.md)**

---

*This documentation system provides comprehensive coverage of the RISC-V multi-core system project. For the most current status and metrics, always refer to [CURRENT_PROJECT_STATUS.md](CURRENT_PROJECT_STATUS.md) as the single source of truth.* 