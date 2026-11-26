module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailNodesGrid
public import Turan.Sturm
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

noncomputable section
namespace Turan

theorem tail_node_pairs (j : ℕ) (hj : 225 ≤ j)
    (h0 : psi j (-1/2) ≠ 0) :
    let η := Real.pi / Real.sqrt (2*(j:ℝ)-1125/100)
    let N := Nat.floor (3/η)
    let w₀ : ℝ := -1/2
    let S := (hermite j).roots.toFinset.filter
      (fun s => s.im = 0 ∧ -(7:ℝ)/2 ≤ s.re ∧ s.re ≤ 5/2)
    ∃ d e : Fin N → ℝ, Function.Injective d ∧ Function.Injective e ∧
      ∀ i, 0 < d i ∧ 0 < e i ∧
        ((w₀ + d i : ℝ) : ℂ) ∈ S ∧
        ((w₀ - e i : ℝ) : ℂ) ∈ S ∧
        d i + e i ≤ (2*(i.val:ℝ)+1)*η := by
  classical
  intro η N w S
  let k := Real.sqrt (2*(j:ℝ)-1125/100)
  have hj' : (225:ℝ) ≤ j := by exact_mod_cast hj
  have hrad : 0 < 2*(j:ℝ)-1125/100 := by linarith
  have hk : 0 < k := Real.sqrt_pos.mpr hrad
  have hk2 : k^2 = 2*(j:ℝ)-1125/100 := Real.sq_sqrt hrad.le
  have hη : 0 < η := div_pos Real.pi_pos hk
  have hη3 : η ≤ 3 := by
    apply (div_le_iff₀ hk).mpr
    have : 2 ≤ k := by
      by_contra! h
      nlinarith only [hk2, hj', mul_pos (by linarith : 0 < 2-k) (by linarith : 0 < 2+k)]
    linarith only [this, Real.pi_lt_four]
  have hN : (N:ℝ)*η ≤ 3 := (le_div_iff₀ hη).mp (Nat.floor_le (by positivity))
  let R := S.image Complex.re
  have mem {x : ℝ} : x ∈ R ↔ (x:ℂ) ∈ S := by
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have him := (Finset.mem_filter.mp hz).2.1
      rwa [show (z.re:ℂ) = z from Complex.ext rfl (by simpa using him.symm)]
    · intro hx
      exact Finset.mem_image.mpr ⟨(x:ℂ), hx, rfl⟩
  have hpoly : hermite j ≠ 0 := fun h => h0 (by simp [psi, h])
  have hw : w ∉ R := by
    intro hw
    have hz := (Finset.mem_filter.mp (mem.mp hw)).1
    have hev := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hz)
    apply h0
    have hwcast : (w:ℂ) = -1/2 := by norm_num [w]
    rw [← hwcast]
    exact div_eq_zero_iff.mpr (Or.inl hev)
  have cell (a : ℝ) (ha : w-3 ≤ a) (hb : a+η ≤ w+3) :
      ∃ t ∈ Set.Ioo a (a+η), t ∈ R := by
    have inside {t : ℝ} (ht : t ∈ Set.Ioo a (a+η)) : -(7:ℝ)/2 < t ∧ t < 5/2 := by
      dsimp [w] at ha hb
      exact ⟨by linarith only [ha, ht.1], by linarith only [hb, ht.2]⟩
    obtain ⟨t, ht, hz⟩ := hermite_sturm_interval j a k hk (by
      intro x hx
      obtain ⟨hx₁, hx₂⟩ := inside hx
      nlinarith only [hk2, mul_pos (by linarith : 0 < x+7/2) (by linarith : 0 < 7/2-x)])
    have hev : (hermite j).eval (t:ℂ) = 0 := (div_eq_zero_iff.mp hz).resolve_right
      (fun h => h0 (div_eq_zero_iff.mpr (Or.inr h)))
    exact ⟨t, ht, mem.mpr (Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hpoly).mpr hev),
       rfl, (inside ht).1.le, (inside ht).2.le⟩)⟩
  obtain ⟨d, e, hd, he, h⟩ := node_pairs_of_occupied_cells R w η N hη hη3 hN hw cell
  refine ⟨d, e, hd, he, fun i => ?_⟩
  obtain ⟨hdp, hep, hr, hl, hpair⟩ := h i
  exact ⟨hdp, hep, mem.mp hr, mem.mp hl, hpair⟩

end Turan
