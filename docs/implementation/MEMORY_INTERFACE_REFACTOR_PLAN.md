# Memory Interface Refactoring Plan
## Protocol-Agnostic Memory Architecture

**Project:** RV32IM Core Memory Interface Refactoring  
**Timeline:** 2-3 weeks  
**Status:** Planning  

---

## 🎯 Goals
- **Protocol Independence:** Abstract memory protocol details from core logic
- **Modularity:** Clean separation between core, cache, and memory interface layers
- **Extensibility:** Easy addition of new protocols (AXI4, CHI, TileLink)
- **Maintainability:** Reduced coupling and improved testability

---

## 🏗️ Current vs Proposed Architecture

### Current (Protocol-Coupled)
```
Fetch Stage → ICache → AXI4 Memory Interface
Mem Stage   → DCache → AXI4 Memory Interface
```

### Proposed (Protocol-Agnostic)
```
Fetch Stage → ICache → Memory Request Interface → Protocol Adapter → AXI4/CHI/TileLink
Mem Stage   → DCache → Memory Request Interface → Protocol Adapter → AXI4/CHI/TileLink
```

---

## 🔧 Key Components

### 1. Memory Request Interface
```systemverilog
interface memory_req_rsp_if;
    // Request
    logic        req_valid, req_ready;
    addr_t       req_addr;
    logic [2:0]  req_size;
    logic        req_write;
    word_t       req_data;
    logic [3:0]  req_strb;
    logic [3:0]  req_id;
    
    // Response
    logic        rsp_valid, rsp_ready;
    word_t       rsp_data;
    logic [3:0]  rsp_id;
    logic        rsp_error;
    
    modport master (output req_*, input rsp_*);
    modport slave  (input req_*, output rsp_*);
endinterface
```

### 2. Cache Interface
```systemverilog
interface cache_if;
    // Cache operations
    logic        req_valid, req_ready;
    addr_t       req_addr;
    logic        req_write;
    word_t       req_data;
    logic [3:0]  req_strb;
    
    logic        rsp_valid, rsp_ready;
    word_t       rsp_data;
    logic        rsp_hit;
    
    // Control
    logic        flush_req, flush_done;
    
    modport master, slave;
endinterface
```

### 3. Protocol Adapters
```systemverilog
// AXI4 Adapter
module axi4_adapter (
    memory_req_rsp_if.master mem_if,
    axi4_if.slave axi4_if
);

// CHI Adapter (Future)
module chi_adapter (
    memory_req_rsp_if.master mem_if,
    chi_if.slave chi_if
);
```

---

## 📁 New File Structure

```
rtl/
├── memory/
│   ├── memory_req_rsp_if.sv    # Protocol-agnostic interface
│   ├── cache_if.sv             # Cache interface
│   └── memory_types.sv         # Common types
├── protocols/
│   ├── axi4_adapter.sv         # AXI4 protocol adapter
│   ├── chi_adapter.sv          # CHI protocol adapter
│   └── protocol_factory.sv     # Protocol selection
└── cache/
    ├── icache.sv               # Uses memory_req_rsp_if
    ├── dcache.sv               # Uses memory_req_rsp_if
    └── cache_controller.sv     # Unified cache control
```

---

## 🔄 Implementation Steps

### Phase 1: Interface Definition (Week 1)
1. Create `memory_req_rsp_if.sv` and `cache_if.sv`
2. Define common types in `memory_types.sv`
3. Implement `axi4_adapter.sv` for backward compatibility

### Phase 2: Cache Refactoring (Week 2)
1. Refactor `icache.sv` to use `memory_req_rsp_if`
2. Create `dcache.sv` with same interface
3. Create `cache_controller.sv` for unified management

### Phase 3: Pipeline Integration (Week 3)
1. Update `fetch_stage.sv` to use `cache_if`
2. Update `mem_stage.sv` to use `cache_if`
3. Update `riscv_core.sv` for new architecture

---

## 📊 Benefits

| Aspect | Current | Refactored | Improvement |
|--------|---------|------------|-------------|
| **Protocol Coupling** | High | Low | ✅ Significant |
| **Code Reuse** | Low | High | ✅ Major |
| **Testability** | Moderate | High | ✅ Significant |
| **Protocol Switching** | Hard | Easy | ✅ Major |

---

## 🧪 Testing Strategy

### Unit Testing
- Interface behavior verification
- Protocol adapter testing
- Cache functionality with new interfaces

### Integration Testing
- Protocol switching verification
- Performance regression testing
- Backward compatibility testing

---

## 🚨 Risks & Mitigation

| Risk | Mitigation |
|------|------------|
| **Performance Regression** | Extensive benchmarking, optimization |
| **Interface Complexity** | Clear documentation, examples |
| **Integration Issues** | Incremental implementation, rollback plan |

---

## 📈 Success Metrics

- **Zero Performance Regression:** Maintain current IPC/latency
- **100% Protocol Compatibility:** Preserve existing AXI4 functionality
- **Clean Separation:** No protocol-specific code in core modules
- **50% Faster Protocol Switching:** Reduced development time

---

## 🔄 Migration Path

1. **Phase 1:** AXI4 adapter maintains current interface
2. **Phase 2:** Core modules work with both interfaces
3. **Phase 3:** Gradual migration to new interfaces
4. **Phase 4:** Remove old interface code

---

## 📝 Next Steps

1. **Review Plan:** Team approval of architecture
2. **Create Interfaces:** Start with `memory_req_rsp_if.sv`
3. **Implement AXI4 Adapter:** Maintain backward compatibility
4. **Begin Cache Refactoring:** Update ICache first

**Ready for implementation when approved.** 