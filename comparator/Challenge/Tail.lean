module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailDefs

@[expose] public section
namespace Turan

theorem lemma_eleven (n m : ℕ) (hm : 450 ≤ m) (hn : 2 ≤ n) (hhalf : 2*n ≤ m)
    (a b c : ℂ) (hs : emptyStrip (normalizedFamily n m a b) (87/100))
    (hc : 1 + 2*c + a*psi n c = 0) (hx : |c.re| ≤ 2) (hy : |c.im| < 76/100) :
    normalizedFamily n m a b c ≠ 0 ∧
    1 < 9000*(m:ℝ)^4 * ‖normalizedFamily n m a b c‖ ∧
    1+‖a‖ < 110000*(m:ℝ)^((9:ℝ)/2) * ‖normalizedFamily n m a b c‖ := by sorry

theorem lemma_fourteen (n m : ℕ) (hm : 450 ≤ m) (hhalf : m ≤ 2*n) (hnm : n < m)
    (a b : ℂ) (hs : emptyStrip (normalizedFamily n m a b) (87/100))
    (z : ℂ) (hz : |z.im| ≤ 7/11) (l : ℕ) (hl : 1 ≤ l) (hl' : l ≤ 4) :
    ‖iteratedDeriv l (normalizedFamily n m a b) z / normalizedFamily n m a b z‖ ≤
      (11 * omega m z)^l := by sorry

theorem lemma_fifteen (n m : ℕ) (hm : 450 ≤ m) (hhalf : m ≤ 2*n) (hnm : n < m)
    (a b : ℂ) (hs : emptyStrip (normalizedFamily n m a b) (87/100))
    (j : ℕ) (hj : j = n ∨ j = m) (z : ℂ) (hz : |z.im| = 7/11) :
    ‖modeQuotient n m j a b z‖ ≤ 4200 * (omega m z)^4 / ((j:ℝ)*(m-n:ℝ)) := by sorry

theorem lemma_sixteen (n m : ℕ) (hm : 450 ≤ m) (hhalf : m ≤ 2*n) (hnm : n < m)
    (a b : ℂ) (hs : emptyStrip (normalizedFamily n m a b) (87/100)) (j : ℕ) (hj : j=n ∨ j=m) :
    ‖modeQuotient n m j a b (-1/2)‖ ≤ 25000*(m:ℝ)^2/((j:ℝ)*(m-n:ℝ))*nodeProduct j := by sorry

theorem lemma_seventeen (j : ℕ) (hj : 225 ≤ j) :
    psi j (-1/2) = 0 ∨
      -Real.log (nodeProduct j) > (608/1000)*Real.sqrt (2*(j:ℝ)-1125/100) - 315/1000 := by sorry

theorem large_upper_index_gap (n m : ℕ) (hm : 450 ≤ m) (hhalf : m ≤ 2*n) (hnm : n < m)
    (a b : ℂ) : ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100 := by sorry

end Turan
