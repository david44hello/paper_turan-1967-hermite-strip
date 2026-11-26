module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.SectionTwoAlgebraDefs

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Turan.SectionTwo
namespace Expansion

variable {ι R S : Type*} [CommRing R] [CommRing S]

/-- Apply the shifts to an abstract derivative vector. The shift with
eigenvalue d raises its leading derivative order by exactly two. -/
def applyWord (x y : R) (d : ι → R) (J : ℕ → R) : List ι → ℕ → R
  | [], l => J l
  | t :: w, l => applyWord x y d J w (l+2) - 2*x*applyWord x y d J w (l+1) +
      (d t - 2*(l : R)*y)*applyWord x y d J w l

def delta (i l : ℕ) : R := if l = i then 1 else 0

theorem map_word (h : R →+* S) (x y : R) (d : ι → R) (J : ℕ → R) (w : List ι) (l : ℕ) :
    h (applyWord x y d J w l) = applyWord (h x) (h y) (h ∘ d) (h ∘ J) w l := by
  induction w generalizing l with
  | nil => rfl
  | cons t w ih => simp [applyWord, ih, map_ofNat]

private theorem above_order (x y : R) (d : ι → R) (w : List ι) (i l : ℕ)
    (hi : l + 2*w.length < i) : applyWord x y d (delta i) w l = 0 := by
  induction w generalizing l with
  | nil => simp [applyWord, delta, show l ≠ i by simpa using (show l < i by simpa using hi).ne]
  | cons t w ih =>
    simp only [List.length_cons] at hi
    simp [applyWord, ih (l+2) (by omega), ih (l+1) (by omega), ih l (by omega)]

theorem leading_one (x y : R) (d : ι → R) (w : List ι) (l : ℕ) :
    applyWord x y d (delta (l+2*w.length)) w l = 1 := by
  induction w generalizing l with
  | nil => simp [applyWord, delta]
  | cons t w ih =>
    simp only [List.length_cons, applyWord]
    rw [above_order x y d w _ (l+1) (by omega), above_order x y d w _ l (by omega),
      show l+2*(w.length+1) = (l+2)+2*w.length by omega, ih]
    ring

/-- Expand a word in coordinate vectors. Bounding the summation range
also records that higher derivatives cannot occur. -/
theorem sum_coordinates (x y : R) (d : ι → R) (J : ℕ → R) (w : List ι) (l N : ℕ)
    (hN : l+2*w.length ≤ N) :
    applyWord x y d J w l =
      ∑ i ∈ Finset.range (N+1), applyWord x y d (delta i) w l * J i := by
  induction w generalizing l with
  | nil =>
    have hl : l ∈ Finset.range (N+1) := Finset.mem_range.mpr (by simpa using (by simpa using hN : l ≤ N))
    simp [applyWord, delta, ite_mul, hl]
  | cons t w ih =>
    simp only [List.length_cons] at hN
    simp only [applyWord]
    rw [ih (l+2) (by omega), ih (l+1) (by omega), ih l (by omega)]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

end Expansion
end Turan.SectionTwo
