# Turán’s Hermite strip problem

The paper’s link is on the [front page of this repository](https://github.com/david44hello/paper_turan-1967-hermite-strip).

Lean proves the sharp strip width and identifies the two extremal polynomials over all degrees, given four certificate inputs from the supplement. The common disk in Proposition 3, the cubic examples that establish sharpness, and the four written low-degree bounds have proofs from Lean’s standard axioms alone.

The [reading guide](WHAT_TO_READ.md) identifies the statements and their assumptions.

## How to verify

Install Git, Python 3 and elan. From the `lean/` directory of the checkout, run

```sh
./scripts/check.sh
```

The command builds the library, prints the type and axioms of each listed theorem, and compares the resulting claim audit with the files in the checkout.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
