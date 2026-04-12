# Benchmark: pre-fused-trampoline

- **Timestamp**: 2026-04-12T15:12:49+02:00
- **Nix**: nix (Nix) 2.31.3
- **System**: Linux 6.12.66 x86_64

## Test Suite
| Benchmark            |     ms |
|----------------------|-------:|
| tests                |  26401 |

## Interpreter
| Benchmark            |     ms |
|----------------------|-------:|
| fib10                |    198 |
| fib15                |    409 |
| fib20                |   1520 |
| lets100              |    179 |
| lets500              |    256 |
| sum100               |    560 |
| sum1000              |   FAIL |
| countdown1000        |    528 |

## Build Simulator
| Benchmark            |     ms |
|----------------------|-------:|
| linear50             |    161 |
| linear100            |    175 |
| linear200            |    197 |
| wide50               |    176 |
| wide100              |    185 |
| wide200              |    227 |
| diamond5             |    177 |
| diamond8             |    186 |
| tree5                |    174 |
| tree8                |    229 |
| mixed_small          |    176 |
| mixed_medium         |    265 |

## Stress Tests
| Benchmark            |    10k |   100k |
|----------------------|-------:|-------:|
| effectHeavy          |    224 |   1905 |
| bindHeavy            |    231 |    609 |
| mixed                |    297 |   2570 |
| rawGC                |     35 |    108 |
