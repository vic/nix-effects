# Bench run: level-step5_6-funext-het

- **Timestamp**: 2026-04-25T14:05:16Z
- **Nix**: 2.31.4
- **System**: x86_64-linux
- **Runs per workload**: 5

| Workload                                  |     values |     thunks |   cpu ms |  wall ms |
|-------------------------------------------|-----------:|-----------:|---------:|---------:|
| effects.buildSim.diamond5                 |     670890 |     228492 |      217 |      288 |
| effects.buildSim.fail_early               |     667760 |     225630 |      211 |      275 |
| effects.buildSim.fail_late                |     667760 |     225630 |      317 |      395 |
| effects.buildSim.fail_mid                 |     667760 |     225630 |      207 |      274 |
| effects.buildSim.linear100                |     688759 |     244640 |      220 |      292 |
| effects.buildSim.linear50                 |     678259 |     235140 |      199 |      258 |
| effects.buildSim.mixed_small              |     698142 |     253049 |      217 |      288 |
| effects.buildSim.tree5                    |     680180 |     236958 |      211 |      277 |
| effects.buildSim.wide100                  |     686488 |     242450 |      218 |      289 |
| effects.buildSim.wide50                   |     677238 |     234150 |      223 |      296 |
| effects.interp.countdown1000              |     949136 |     483990 |      258 |      333 |
| effects.interp.fib10                      |     728808 |     281732 |      243 |      320 |
| effects.interp.fib15                      |    1347530 |     850166 |      322 |      407 |
| effects.interp.lets100                    |     684890 |     241667 |      245 |      327 |
| effects.interp.lets500                    |     753290 |     305667 |      305 |      385 |
| effects.interp.sum100                     |     705845 |     260499 |      238 |      318 |
| effects.interp.sum1000                    |    1045145 |     570999 |      297 |      382 |
| effects.stress.bindHeavy.s10k             |     976297 |     474170 |      268 |      331 |
| effects.stress.deepChains.s10k            |     737640 |     255534 |      212 |      280 |
| effects.stress.effectHeavy.s10k           |     937773 |     475644 |      255 |      322 |
| effects.stress.mixed.s10k                 |    1227774 |     735645 |      293 |      370 |
| effects.stress.nestedHandlers.d3_i1k      |     728836 |     277704 |      211 |      278 |
| effects.stress.rawGC.s10k                 |      50171 |      50047 |       24 |       45 |
| tc.bindP.slow-path-chain-5000             |     933355 |     476118 |      226 |      296 |
| tc.check.list-chain-5000                  |    3816977 |    3264019 |      812 |      936 |
| tc.check.macro-field                      |     693949 |     250822 |      273 |      339 |
| tc.check.nat-chain-5000                   |    1140590 |     652774 |      273 |      350 |
| tc.conv.alpha-equivalent                  |     669864 |     227102 |      240 |      319 |
| tc.conv.beta-distinct                     |     671393 |     228500 |      223 |      291 |
| tc.conv.identical-deep                    |    1140593 |     652777 |      277 |      356 |
| tc.conv.identical-shallow                 |     670593 |     227716 |      241 |      307 |
| tc.conv.mu-heavy                          |     672915 |     229598 |      251 |      322 |
| tc.conv.plus-heavy                        |     673004 |     230125 |      234 |      309 |
| tc.diag.hint-resolve-5000                 |     796389 |     338806 |      253 |      353 |
| tc.diag.pretty-multi-line-5000            |     800450 |     338232 |      235 |      348 |
| tc.diag.pretty-one-line-5000              |     771406 |     309192 |      235 |      340 |
| tc.e2e.datatype-macro-big                 |     693952 |     250825 |      216 |      272 |
| tc.e2e.datatypeI-fin-deep                 |     778805 |     332148 |      237 |      295 |
| tc.e2e.let-chain-100                      |     745720 |     302239 |      230 |      290 |
| tc.e2e.tc-test-suite-full                 |   17174466 |   15543369 |     3792 |     3621 |
| tc.e2e.tc-test-suite-per-module.check     |    1256643 |     654529 |      394 |      554 |
| tc.e2e.tc-test-suite-per-module.conv      |     971155 |     410602 |      273 |      338 |
| tc.e2e.tc-test-suite-per-module.elaborate |   11927152 |   10969068 |     2734 |     2679 |
| tc.e2e.tc-test-suite-per-module.eval      |     829265 |     297699 |      250 |      326 |
| tc.e2e.tc-test-suite-per-module.hoas      |    3434099 |    2717533 |      678 |      800 |
| tc.e2e.tc-test-suite-per-module.quote     |    1059704 |     509205 |      267 |      340 |
| tc.e2e.tc-test-suite-per-module.term      |     708231 |     247826 |      236 |      305 |
| tc.e2e.tc-test-suite-per-module.value     |     708146 |     247741 |      243 |      310 |
| tc.e2e.tc-test-suite-per-module.verified  |    1955175 |    1471482 |      475 |      568 |
| tc.elaborate.flatten                      |     681873 |     231372 |      211 |      281 |
| tc.elaborate.recursive                    |     731206 |     276636 |      220 |      284 |
| tc.infer.deep-app-100                     |     763406 |     319028 |      241 |      306 |
| tc.quote.closed                           |     689491 |     245151 |      225 |      296 |
| tc.quote.open                             |     670748 |     227895 |      212 |      275 |
| tc.quote.stuck                            |     676130 |     232985 |      220 |      291 |

