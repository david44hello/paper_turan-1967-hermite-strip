# What to read

Start with the [claim audit](AUDIT.md). The [claim map](CLAIM_MAP.tsv) gives the location in the short paper, the conclusion and the Lean declaration for each public target. The separate [proof-step census](PROOF_STEPS.tsv) records the status and evidence for additional printed formulas, cited facts and calculations. The formal statements use the existence of a zero with the stated imaginary part. For a nonconstant polynomial, `polynomial_has_lowest_zero` proves that the minimum in the paper’s definition of height is attained.

## The all-degree statements

[Main.lean](Turan/Main.lean) proves the closed-strip bound for every degree pair and coefficient pair, the two strict bounds in Proposition 2, and the classification of equality. [Coverage.lean](Turan/Coverage.lean) identifies the least working width and the set of actual extremal polynomials. [Attained.lean](Turan/Attained.lean) proves that h is the greatest value among the minimum root heights attained by individual family members. The all-degree upper bound and equality classification take G1, MiddleChecks, F1 and E10 as explicit hypotheses. The lower bound proving sharpness uses only the two cubic examples.

## The disk and the cubic extremizers

[Disk.lean](Turan/Disk.lean) proves Proposition 3 with a single radius for every choice of indices and coefficients. The proof uses the Hermite differential equation to isolate the highest-degree term. Its many real zeros give a small bound for its contribution on the inner disk. Applying this bound twice supplies a zero of the full polynomial. This argument is independent of the supplement. Disk.lean proves Proposition 3 by a different argument from the compactness proof in Section 2.

[Cubic.lean](Turan/Cubic.lean) proves that every polynomial of degrees (2,3) has a zero in the closed strip and identifies the two coefficient pairs that can avoid the open strip. [Extremal.lean](Turan/Extremal.lean) factors both cubics and proves that their only zeros have height exactly h. These two distinct examples already rule out every smaller width. [Constants.lean](Turan/Constants.lean) proves the closed form for h and [Decimal.lean](Turan/Decimal.lean) certifies its printed digits.

[SlotFilter.lean](Turan/SlotFilter.lean) also proves the original Section 2 filter claim. For the varying four-slot sequences in the proof, the quotient of the filtered and original polynomials tends uniformly to one on every fixed circle, and the filtered polynomials eventually have no zeros in the closed disk.

## The other index pairs

[Quintic.lean](Turan/Quintic.lean) proves the strict bound 87/100 for every choice of coefficients in degrees (2,5). [TailUpper.lean](Turan/TailUpper.lean) proves the same bound for 450 ≤ m and m ≤ 2n, without a computation premise. [LowerTail.lean](Turan/LowerTail.lean) covers all upper degrees m ≥ 450. Its lower-index argument uses the finite trinomial computation described below.

The Gaussian moment argument for Lemma 9 is in [Mehler.lean](Turan/Mehler.lean). The energy estimate for Lemma 12 and the circle estimate for Lemma 13 are in [Vertical.lean](Turan/Vertical.lean) and [Volterra.lean](Turan/Volterra.lean). [Rouche.lean](Turan/Rouche.lean) proves polynomial Rouché comparison with multiplicities, using the [polynomial argument principle](Turan/Argument.lean).

## Finite computations

The paper’s supplement *Proof records for the Hermite strip problem* supplies certificates and verifier programs. Its `READ_FIRST.txt` identifies the inputs and expected outputs. The machine checks enter the formal statements as named hypotheses. The computations and their analytic consequences have distinct entries in the claim audit.

* `TrinomialDiskCheck` specifies the coefficient inequalities of G1 for degrees 4 through 79, in both coefficient charts. Its hypothesis ends with strict dominance of one Taylor coefficient on each certified disk. Lean deduces the zero and its bounds. The two low degrees and all degrees at least 80 have separate proofs.
* `MiddleChecks` covers all 100,118 pairs with 7 ≤ m ≤ 449. For each pair the supplement provides one of four kinds of evidence. The [circle](Turan/CircleCertificate.lean), [ratio-chart](Turan/Ratio.lean), [transfer](Turan/Transfer.lean) and [winding](Turan/Winding.lean) proofs each turn the corresponding coefficient inequalities or nominal polygon tally into a root in the strict strip.
* `SexticChartCheck` and `QuinticChartCheck` describe E10 and F1. Each fixes one coefficient of the certificate basis, covers the two remaining complex coefficients, and specifies the dominant Taylor term and strip height. The sextic bases are given in [ProjectiveDefs.lean](Turan/ProjectiveDefs.lean). [Projective.lean](Turan/Projective.lean) proves the changes of basis for all four index pairs.
* The separate arbitrary-perturbation statement uses `UniformTransferCheck`, the uniform margin part of C1. Its one selected disk works for every polynomial perturbation whose modulus stays below 1/64 throughout the disk of radius 5/4. The all-degree theorem uses the paired-circle consequence within `MiddleChecks`. The [archived verifier outputs](checks/README.md) distinguish these uses.

## Verification

The reader command builds the library from its pinned sources, prints the full type and axioms of each listed theorem, and compares the certificate inputs and audit files with the checkout. [Reader instructions](README.md)

For the release, the verification team checks a clean committed copy. The kernel replay covers the compiled Lean modules and a single export of their declarations. The independent comparator checks the solution against the reviewed challenge, first with its default kernel and then with its paranoid checkers. The proof-step census gives the mathematical evidence for each passage, including the four explicit finite inputs. [Independent comparator](../comparator/README.md)

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
