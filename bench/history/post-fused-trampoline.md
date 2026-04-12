# Benchmark: post-fused-trampoline

- **Timestamp**: 2026-04-12T15:47:26+02:00
- **Nix**: nix (Nix) 2.31.3
- **System**: Linux 6.12.66 x86_64

## Test Suite
| Benchmark            |     ms |
|----------------------|-------:|
| tests                |  25150 |

## Interpreter
| Benchmark            |     ms |
|----------------------|-------:|
| fib10                |    202 |
| fib15                |    318 |
| fib20                |   1528 |
| lets100              |    220 |
| lets500              |    359 |
| sum100               |    573 |
| sum1000              |    686 |
| countdown1000        |    244 |

## Build Simulator
| Benchmark            |     ms |
|----------------------|-------:|
| linear50             |    186 |
| linear100            |    211 |
| linear200            |    198 |
| wide50               |    195 |
| wide100              |    187 |
| wide200              |    429 |
| diamond5             |    597 |
| diamond8             |    611 |
| tree5                |    206 |
| tree8                |    262 |
| mixed_small          |    203 |
| mixed_medium         |    281 |

## Stress Tests
| Benchmark            |    10k |   100k |
|----------------------|-------:|-------:|
| effectHeavy          |    253 |   1642 |
| bindHeavy            |    238 |    649 |
| mixed                |    313 |   2095 |
| rawGC                |     32 |    108 |
