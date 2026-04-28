# Bench run: baseline

- **Timestamp**: 2026-04-25T08:22:04Z
- **Nix**: 2.31.4
- **System**: x86_64-linux
- **Runs per workload**: 50

| Workload                                  |     values |     thunks |   cpu ms |  wall ms |
|-------------------------------------------|-----------:|-----------:|---------:|---------:|
| effects.buildSim.diamond5                 |     670890 |     228492 |      202 |      259 |
| effects.buildSim.fail_early               |     667760 |     225630 |      207 |      275 |
| effects.buildSim.fail_late                |     667760 |     225630 |      206 |      272 |
| effects.buildSim.fail_mid                 |     667760 |     225630 |      200 |      264 |
| effects.buildSim.linear100                |     688759 |     244640 |      204 |      265 |
| effects.buildSim.linear50                 |     678259 |     235140 |      202 |      260 |
| effects.buildSim.mixed_small              |     698142 |     253049 |      219 |      283 |
| effects.buildSim.tree5                    |     680180 |     236958 |      217 |      281 |
| effects.buildSim.wide100                  |     686488 |     242450 |      205 |      268 |
| effects.buildSim.wide50                   |     677238 |     234150 |      212 |      276 |
| effects.interp.countdown1000              |     949136 |     483990 |      249 |      324 |
| effects.interp.fib10                      |     728808 |     281732 |      209 |      271 |
| effects.interp.fib15                      |    1347530 |     850166 |      308 |      381 |
| effects.interp.lets100                    |     684890 |     241667 |      200 |      259 |
| effects.interp.lets500                    |     753290 |     305667 |      270 |      336 |
| effects.interp.sum100                     |     705845 |     260499 |      204 |      266 |
| effects.interp.sum1000                    |    1045145 |     570999 |      259 |      334 |
| effects.stress.bindHeavy.s10k             |     976297 |     474170 |      233 |      302 |
| effects.stress.deepChains.s10k            |     737640 |     255534 |      199 |      262 |
| effects.stress.effectHeavy.s10k           |     937773 |     475644 |      234 |      302 |
| effects.stress.mixed.s10k                 |    1227774 |     735645 |      275 |      344 |
| effects.stress.nestedHandlers.d3_i1k      |     728836 |     277704 |      202 |      262 |
| effects.stress.rawGC.s10k                 |      50171 |      50047 |       29 |       46 |
| tc.bindP.slow-path-chain-5000             |     933355 |     476118 |      223 |      292 |
| tc.check.list-chain-5000                  |    3816954 |    3264008 |      814 |      938 |
| tc.check.macro-field                      |     693866 |     250751 |      215 |      278 |
| tc.check.nat-chain-5000                   |    1140567 |     652763 |      263 |      333 |
| tc.conv.alpha-equivalent                  |     669841 |     227091 |      209 |      273 |
| tc.conv.beta-distinct                     |     671370 |     228489 |      206 |      268 |
| tc.conv.identical-deep                    |    1140570 |     652766 |      264 |      334 |
| tc.conv.identical-shallow                 |     670570 |     227705 |      212 |      280 |
| tc.conv.mu-heavy                          |     672892 |     229587 |      211 |      276 |
| tc.conv.plus-heavy                        |     672981 |     230114 |      209 |      269 |
| tc.diag.hint-resolve-5000                 |     796296 |     338801 |      224 |      336 |
| tc.diag.pretty-multi-line-5000            |     800447 |     338231 |      227 |      334 |
| tc.diag.pretty-one-line-5000              |     771403 |     309191 |      217 |      328 |
| tc.e2e.datatype-macro-big                 |     693869 |     250754 |      223 |      289 |
| tc.e2e.datatypeI-fin-deep                 |     778739 |     332094 |      243 |      316 |
| tc.e2e.let-chain-100                      |     745697 |     302228 |      228 |      295 |
| tc.e2e.tc-test-suite-full                 |   17078897 |   15449644 |     3818 |     3562 |
| tc.e2e.tc-test-suite-per-module.check     |    1252033 |     650315 |      398 |      571 |
| tc.e2e.tc-test-suite-per-module.conv      |     970428 |     410235 |      269 |      351 |
| tc.e2e.tc-test-suite-per-module.elaborate |   11926507 |   10968775 |     2802 |     2775 |
| tc.e2e.tc-test-suite-per-module.eval      |     828661 |     297447 |      251 |      324 |
| tc.e2e.tc-test-suite-per-module.hoas      |    3348196 |    2633391 |      642 |      754 |
| tc.e2e.tc-test-suite-per-module.quote     |    1059101 |     508954 |      276 |      352 |
| tc.e2e.tc-test-suite-per-module.term      |     707605 |     247552 |      230 |      299 |
| tc.e2e.tc-test-suite-per-module.value     |     707578 |     247525 |      234 |      302 |
| tc.e2e.tc-test-suite-per-module.verified  |    1948893 |    1465734 |      479 |      574 |
| tc.elaborate.flatten                      |     681848 |     231361 |      205 |      271 |
| tc.elaborate.recursive                    |     731181 |     276625 |      215 |      281 |
| tc.infer.deep-app-100                     |     763383 |     319017 |      233 |      300 |
| tc.quote.closed                           |     689468 |     245140 |      229 |      298 |
| tc.quote.open                             |     670725 |     227884 |      216 |      284 |
| tc.quote.stuck                            |     676107 |     232974 |      226 |      294 |

