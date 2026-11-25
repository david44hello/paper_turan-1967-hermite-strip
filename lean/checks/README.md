# Certificate replay records

These are the verifier outputs for the arithmetic in the short paper. The frozen supplement *Proof records for the Hermite strip problem*, version 0.93, has archive MD5 `ca149937519a7d3add22589c9e0d99f2`. Its `READ_FIRST.txt` maps the statements in the paper to the programs and describes how to reproduce each calculation.

| Lean input | Verifier records | What the arithmetic supplies |
|---|---|---|
| `TrinomialDiskCheck` | [G1](G1.log) | Dominance of a positive-order Taylor coefficient on disks for both coefficient charts and degrees 4 through 79. The 6,598 leaves have largest height numerator 7,753 over 10,240. |
| `MiddleChecks`, circle class | [A1](A1.log), [A2](A2.log), [A3](A3.log) | The retained narrow circles and the repaired circle systems give 96,816 degree pairs. The two phase sectors have infeasible systems of linear inequalities. |
| `MiddleChecks`, ratio charts | [B1](B1.log), [B2](B2.log), [B3](B3.log) | In 429 degree pairs, the coefficient bounds give a dominant Taylor pivot on a suitable disk under the stated inverse-scale bound. |
| `MiddleChecks`, transfer from a trinomial | [C1](C1.log) | 2,524 pairs use a uniform transfer inequality and 75 pairs use square-specific bounds. |
| `MiddleChecks`, winding and disk leaves | [D1](D1.log), [D2](D2.log) | 265 pairs and nine quadratic-index pairs use segment enclosures with a positive nominal polygon crossing tally, or a positive Taylor pivot. |
| `MiddleChecks`, coverage | [R00](R00.log) | The archive lists are disjoint and cover all 100,118 pairs with 7 ≤ m ≤ 449. |
| `SexticChartCheck` | [E10](E10.log) | Projective disk checks for (2,6), (3,6), and (4,6). The PARI verifier checks the sharper height for (2,6); the Python replay for that pair checks the same cover below 9/10. |
| `QuinticChartCheck` | [F1](F1.log) | The projective disks in the (3,5) cover have height at most 29,491/32,768. |

All 39 checks passed on a fresh extract of the frozen archive. The log files in this directory are the outputs from that run. The partition check R00 covers the 100,118 middle-degree pairs. The optional J3 check compares the quartic substitution with its defining expression and verifies that its proportionality constant is nonzero. The four certificate hypotheses and their analytic consequences are listed separately in the claim audit.
