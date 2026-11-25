-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.TrinomialAE

noncomputable section
open Metric Set
open scoped ComplexConjugate
namespace Turan.TrinomialAE

private theorem pencil_eval_at (n : ℕ) (a z : ℂ) :
    (G n a).eval z = 1+2*z+a*psi n z := by
  simp [G, Polynomial.eval_add, Polynomial.eval_mul, Giroux.mode_eval]

private theorem reflected_pencil (n : ℕ) (a z : ℂ) :
    reflectedValue (G n a) z = (G n (conj a)).eval z := by
  have hv : psi n (conj z) = conj (psi n z) := by simp [psi,(hermite_symmetry n z).1]
  simp [reflectedValue,pencil_eval_at,hv,map_ofNat]

private theorem pencil_boundary_ratios (n : ℕ) (hn : 80 ≤ n) (a : ℂ) (ha : a ≠ 0)
    (hfree : ∀ z ∈ ball (w₀:ℂ) outerRadius, (G n a).eval z ≠ 0)
    (z : ℂ) (hz : z ∈ sphere (w₀:ℂ) R) :
    ‖(G n a).eval z / reflectedValue (G n a) z‖ < 90*n ∧
      ‖reflectedValue (G n a) z / (G n a).eval z‖ < 90*n := by
  have hout (u : ℂ) (hu : u ∈ ball z clearance) : u ∈ ball (w₀:ℂ) outerRadius := by
    have hdist := dist_triangle u z (w₀:ℂ)
    rw [mem_sphere.mp hz] at hdist
    exact (mem_ball.mpr (by linarith only [mem_ball.mp hu,hdist,
      show clearance + R = outerRadius by norm_num]))
  have hlocal (b : ℂ) (hb : b = a ∨ b = conj a) (u : ℂ) (hu : u ∈ ball z clearance) :
      (G n b).eval u ≠ 0 := by
    have hb' := hout u hu
    rcases hb with rfl | rfl
    · exact hfree u hb'
    · rw [← reflected_pencil]
      change conj ((G n a).eval (conj u)) ≠ 0
      have hc : conj u ∈ ball (w₀:ℂ) outerRadius := by
        rwa [mem_ball, ← Complex.conj_ofReal w₀, Complex.dist_conj_conj]
      simpa using hfree (conj u) hc
  have H := reciprocal_ratios n hn a z ha hz hlocal
  obtain ⟨h₁,h₂,h₃⟩ := H a (Or.inl rfl)
  obtain ⟨h₄,h₅,h₆⟩ := H (conj a) (Or.inr rfl)
  rw [reflected_pencil]
  exact ⟨by simpa only [Complex.conj_conj] using h₄.trans_lt (h₅.trans h₆),
    h₁.trans_lt (h₂.trans h₃)⟩

/-- The phase integration in A.1 (E) at the actual consecutive Hermite zeros. -/
theorem pencil_integrated_obstruction (n : ℕ) (hn : 80 ≤ n) (a : ℂ) (ha : a.im ≠ 0)
    (hfree : ∀ z ∈ ball (w₀:ℂ) outerRadius, (G n a).eval z ≠ 0) :
    ∃ (s₁ s₂ : ℝ) (θ : ℝ → ℝ),
      IsGreatest {s : ℝ | s ∈ Icc (w₀-beta n) w₀ ∧ psi n (s:ℂ)=0} s₁ ∧
      IsLeast {s : ℝ | s ∈ Icc w₀ (w₀+beta n) ∧ psi n (s:ℂ)=0} s₂ ∧
      s₁ < w₀ ∧ w₀ < s₂ ∧ s₂-s₁ < beta n ∧ PhaseOn θ (G n a) diameter ∧
      |θ s₂-θ s₁| = Real.pi ∧
      Real.pi ≤ (2*logBound n/Real.pi)*(J (w₀-s₁)+J (s₂-w₀)) ∧
      (2*logBound n/Real.pi)*(J (w₀-s₁)+J (s₂-w₀)) ≤ (2*logBound n/Real.pi)*J (beta n) ∧
      Real.pi^2 ≤ 2*logBound n*J (beta n) := by
  have ha₀ : a ≠ 0 := fun he => ha (by simp [he])
  have hcenter : psi n (w₀:ℂ) ≠ 0 := by
    intro he
    have hnz := hfree _ (mem_ball_self (by norm_num : 0 < outerRadius))
    apply hnz
    rw [pencil_eval_at,he]
    norm_num [w₀]
  obtain ⟨s₁,s₂,hleft,hright,hs₁,hs₂,hgapfree,hgap⟩ := consecutive_nodes n hn hcenter
  have hβ : beta n < R := by
    have hn' : (80:ℝ) ≤ n := by exact_mod_cast hn
    have hk : 12 ≤ Real.sqrt (2*(n:ℝ)) := Real.le_sqrt_of_sq_le (by linarith)
    apply (div_lt_iff₀ (by linarith : 0 < Real.sqrt (2*(n:ℝ)))).mpr
    dsimp only [R]
    linarith only [Real.pi_lt_d2,hk]
  have hsub : Icc s₁ s₂ ⊆ diameter := by
    intro t ht
    exact ⟨by linarith [hleft.1.1.1,ht.1],by linarith [hright.1.1.2,ht.2]⟩
  obtain ⟨L,_,hlog⟩ := outer_log _ hfree
  let f := fun z => L z - conj (L (conj z))
  have hf : LogOn f (fun z => (G n a).eval z / reflectedValue (G n a) z) (ball (w₀:ℂ) outerRadius) := hlog
  have hbound := (closed_log_bound (G n a) n hn f hf (pencil_boundary_ratios n hn a ha₀ hfree)).2
  obtain ⟨⟨θ,hθ⟩,hdθ⟩ := diameter_derivative (G n a) f hf
  have hdiff : DifferentiableOn ℝ θ diameter := fun t ht =>
    ((hdθ θ hθ t ht).1).differentiableAt.differentiableWithinAt
  have hrestrict : PhaseOn θ (G n a) (Icc s₁ s₂) :=
    ⟨hθ.1.mono hsub,fun t ht => hθ.2 t (hsub ht)⟩
  have hchange := (exact_phase_change n a ha s₁ s₂ hs₁ hs₂ hleft.1.2 hright.1.2 hgapfree).2.2.2 θ hrestrict
  have hder (t : ℝ) (ht : t ∈ Icc s₁ s₂) :
      |deriv θ t| ≤ (2*logBound n/Real.pi)*R/(R^2-(t-w₀)^2) :=
    (phase_derivative_bound n hn (G n a) f hf
      (fun z hz => (hbound z (ball_subset_closedBall hz)).2) θ hθ t (hsub ht)).2
  exact ⟨s₁,s₂,θ,hleft,hright,hs₁,hs₂,hgap,hθ,hchange,
    integrated_obstruction n (by omega) hβ θ s₁ s₂ hs₁ hs₂ hgap hdiff hder hchange⟩

#print axioms pencil_integrated_obstruction

end Turan.TrinomialAE
