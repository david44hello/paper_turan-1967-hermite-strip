# Audit notes

The source is the short edition of *Turán’s Hermite strip problem*, v5.40. The flat TeX has MD5 `a86117bef89fac427fade04217bf1ba4` and the PDF has MD5 `aedd432834412624e40302f3769f7dde`. The expanded edition’s sharp second-place constant is outside the short paper’s main theorem. Figure 1 uses red for candidates excluded as the least half-width. Below h the counterexample is unconditional. At h the guarantee uses the four checks, and every wider strip contains the same zero. The v5.40 claim map also identifies the multiset product in the small-pair summary.

## Mathematical scope

The [claim map](CLAIM_MAP.tsv) identifies passages by their printed subject and source label. Line numbers refer specifically to the frozen v5.40 flat TeX. The map quotes the printed words for the sextic chart basis, the two numerical passages in Appendix A.1, the reciprocal estimate and the zero-stage bound in Appendix A.2. The source polynomial is the physicists’ Hermite polynomial. Its recurrence, complex coefficients, and the cases in which a coefficient vanishes are part of the formalization. The least-width assertion quantifies over all admissible degrees and coefficients. The equality statement identifies two distinct polynomials.

## Proofs that use another route

* Proposition 3 uses high-degree suppression on a fixed disk. The Hermite differential operator isolates the highest mode. Factoring out Sturm-separated real zeros bounds its contribution on an inner disk. Applying this first to trinomials, then to quadrinomials, gives a uniform radius. The proof yields existence without a numerical value of that radius.
* Lemma 7 uses the positive increments of two polynomial boundary margins as the imaginary part moves into the half-plane. Analyticity is checked at every point, including the boundary.
* Lemma 9 uses integration by parts and Cauchy–Schwarz for Gaussian polynomial moments. The Gaussian integral reproduces each individual Hermite polynomial and gives the fourth-root factor in the stated estimate.
* Lemma 12 bounds the energy of consecutive normalized modes along the straight segment from zero to the evaluation point. Lemma 13 uses a scalar differential comparison after integrating the second-derivative bound twice.
* The calculations for individual written low-degree bounds are distinct from the external arithmetic checks used for the finite covers. For the latter, the formal hypotheses and the archived verifier outputs are listed in the [certificate replay records](checks/README.md).

The paper’s corresponding analytic steps also have separate declarations. They include the half-disk maximum principle and its application to the third-root map, the Mehler continuation from the real plane and the weighted estimate obtained by taking a square root on the diagonal, and the removable strip quotient with the sharper boundary constant. The claim map lists the names for each passage.

The Lean comparator checks agreement with the challenge declarations. Matching a declaration to the paper, including its hypotheses, is a separate mathematical review. The printed type of each target and the names of its axioms are available from the reader command.
