# Comparing the Turán statements and proofs

The files in `Challenge/` state the results to be checked. The target theorem names are in `comparator.json`. Lake compares each theorem statement and follows the definitions it uses. The empty `definition_names` list makes every such definition subject to the body comparison. The three permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The statement of Lemma 10 takes the supplement’s computation G1 as an explicit hypothesis, `TrinomialDiskCheck`. For degrees 4 through 79, G1 supplies disks on which one Taylor coefficient dominates. The Lean statement deduces a zero in the required rectangle. The separate statements for degrees 2–3 and degrees at least 80 have no G1 hypothesis. Lemma 8 also carries G1 because its case with 2n ≤ m uses Lemma 10.

The bound for (3,5) uses `QuinticChartCheck` from F1. The bounds for (2,6), (3,6) and (4,6) use `SexticChartCheck` from E10. These hypotheses give coefficient inequalities on disks for the three normalized coefficient charts of each family.

For degrees 7 through 449, `MiddleChecks` states that each admissible pair has a circle, ratio-chart, transfer or winding certificate. These supply inequalities between coefficients or a positive crossing count for a polygon with checked edge bounds. The supplement identifies the pairs and gives the arithmetic checks. The all-degree upper bound and the classification of extremizers take `MiddleChecks` and the G1, F1 and E10 hypotheses. Sharpness itself has an explicit cubic witness.

The statement about arbitrary polynomial perturbations uses `UniformTransferCheck`, the uniform part of the C1 transfer computation. It gives a disk with a coefficient margin greater than 1/64. The chosen disk then works for every perturbation satisfying the stated bound.

On Linux with elan, Git and bubblewrap installed, run these commands from the top of a clean checkout of the release.

```sh
set -eu
comparison_dir=$(mktemp -d)
git archive HEAD:lean | tar -xf - -C "$comparison_dir"
cp -R comparator/Challenge comparator/Challenge.lean comparator/comparator.json comparator/lakefile.toml "$comparison_dir/"
cd "$comparison_dir"
lake exe cache get
lake --no-cache comparator --config=comparator.json --paranoid
```

Lake compares the declarations and checks the proofs. On success its last line reads `Your solution is okay!`.
