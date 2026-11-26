module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Degree
public import Turan.GirouxJacobi
public import Turan.SlotDefs
public import Turan.Sturm
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Complex.Harmonic.Analytic
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Topology.Covering.AddCircle

@[expose] public section

/-! The disk argument for the large-degree trinomial in Appendix A.1. -/

noncomputable section
open Polynomial Metric Set
open scoped ComplexConjugate
namespace Turan.TrinomialAE

abbrev w₀ : ℝ := -1/2
abbrev R : ℝ := 65/100
abbrev outerRadius : ℝ := 76/100
abbrev clearance : ℝ := 11/100
abbrev diameter : Set ℝ := Ioo (w₀-R) (w₀+R)

/-- Giroux.mode_eval identifies the last summand with a times ψₙ. -/
def G (n : ℕ) (a : ℂ) : Polynomial ℂ := 1 + 2*X + C a * Giroux.mode n

def reflectedValue (p : Polynomial ℂ) (z : ℂ) : ℂ := conj (p.eval (conj z))

def LogOn (f g : ℂ → ℂ) (D : Set ℂ) : Prop :=
  AnalyticOnNhd ℂ f D ∧ ∀ z ∈ D, Complex.exp (f z) = g z

/-- A real-valued continuous lift of the argument, allowing any choice at the initial point. -/
def PhaseOn (θ : ℝ → ℝ) (p : Polynomial ℂ) (S : Set ℝ) : Prop :=
  ContinuousOn θ S ∧ ∀ t ∈ S, p.eval (t:ℂ) ≠ 0 ∧
    (θ t : Real.Angle) = ((p.eval (t:ℂ)).arg : Real.Angle)

def logBound (x : ℝ) := Real.log (90*x)
def beta (x : ℝ) := Real.pi / Real.sqrt (2*x)
def J (u : ℝ) := Real.artanh (u/R)

def normalizedLog (n : ℕ) (f : ℂ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * (f z - f (t:ℂ)) / ((4*logBound n : ℝ):ℂ)

/-- The second derivative removes two distinct occurrences of linear factors.
    For k roots this gives k(k−1) ordered choices, counted with multiplicity. -/
private theorem separated_product_derivatives (a z : ℂ) (D : ℝ) (hD : 0 ≤ D)
    (s : Multiset ℂ) (p : Polynomial ℂ) (hp : p = C a * (s.map (X - C ·)).prod)
    (hsep : ∀ w ∈ s, 1 ≤ D * ‖z-w‖) :
    ‖p.derivative.eval z‖ ≤ s.card * D * ‖p.eval z‖ ∧
    ‖p.derivative.derivative.eval z‖ ≤ ((s.card : ℝ) * (s.card - 1)) * D^2 * ‖p.eval z‖ := by
  induction s using Multiset.induction_on generalizing p with
  | empty => simp [hp]
  | cons w s ih =>
    let q := C a * (s.map (X - C ·)).prod
    have hfac : p = (X - C w) * q := by rw [hp]; simp [q, mul_left_comm]
    obtain ⟨h₁, h₂⟩ := ih q rfl (fun v hv => hsep v (Multiset.mem_cons_of_mem hv))
    have hw := hsep w (Multiset.mem_cons_self ..)
    have h₀ : ‖q.eval z‖ ≤ D * ‖z-w‖ * ‖q.eval z‖ := by
      simpa using mul_le_mul_of_nonneg_right hw (norm_nonneg (q.eval z))
    simp only [hfac, derivative_mul, derivative_add, derivative_X_sub_C, one_mul,
      eval_add, eval_mul, eval_sub, eval_X, eval_C, norm_mul, Multiset.card_cons, Nat.cast_add,
      Nat.cast_one]
    constructor
    · calc
        _ ≤ ‖q.eval z‖ + ‖(z-w)*q.derivative.eval z‖ := norm_add_le ..
        _ ≤ D * ‖z-w‖ * ‖q.eval z‖ + ‖z-w‖*(s.card*D*‖q.eval z‖) := by
          rw [norm_mul]; exact add_le_add h₀ (mul_le_mul_of_nonneg_left h₁ (norm_nonneg _))
        _ = _ := by ring
    · have h₁' := h₁.trans (mul_le_mul_of_nonneg_left h₀ (show 0 ≤ (s.card : ℝ) * D by positivity))
      calc
        _ ≤ ‖q.derivative.eval z‖ + (‖q.derivative.eval z‖ +
            ‖z-w‖ * ‖q.derivative.derivative.eval z‖) := by
          grw [norm_add_le, norm_add_le, norm_mul]
        _ ≤ _ := by
          nlinarith only [h₁', mul_le_mul_of_nonneg_left h₂ (norm_nonneg (z-w))]

theorem boundary_derivatives (p : Polynomial ℂ) (n : ℕ) (hn : 80 ≤ n)
    (hdeg : p.natDegree ≤ n) (z : ℂ) (hz : z ∈ sphere (w₀:ℂ) R)
    (hlocal : ∀ w ∈ ball z clearance, p.eval w ≠ 0) :
    (∀ w ∈ p.roots, clearance ≤ ‖z-w‖) ∧ ‖z‖ ≤ 1.15 ∧
    ‖p.derivative.eval z / p.eval z‖ ≤ (n:ℝ)/clearance ∧
    ‖p.derivative.derivative.eval z / p.eval z‖ ≤
      (n:ℝ)*((n:ℝ)-1)/clearance^2 ∧
    ‖(removeMode n p).eval z / p.eval z‖ ≤
      1 + 1.15/clearance + ((n:ℝ)-1)/(2*clearance^2) ∧
    1 + 1.15/clearance + ((n:ℝ)-1)/(2*clearance^2) < 43*(n:ℝ) := by
  have hp := hlocal z (mem_ball_self (by norm_num : 0 < clearance))
  have hsep (w : ℂ) (hw : w ∈ p.roots) : clearance ≤ ‖z-w‖ := by
    by_contra! h
    exact hlocal w (by simpa [mem_ball, dist_comm w z, dist_eq_norm] using h) (isRoot_of_mem_roots hw)
  have hD : 0 < clearance := by norm_num
  have hz' : ‖z‖ ≤ 1.15 := by
    have h := norm_add_le (z-(w₀:ℂ)) (w₀:ℂ)
    rw [sub_add_cancel, ← dist_eq_norm, mem_sphere.mp hz] at h
    norm_num [R, w₀] at h ⊢
    exact h
  have hcard : (p.roots.card : ℝ) ≤ n := by exact_mod_cast (p.card_roots'.trans hdeg)
  obtain ⟨h₁,h₂⟩ := separated_product_derivatives p.leadingCoeff z clearance⁻¹ (inv_nonneg.mpr hD.le)
    p.roots p (IsAlgClosed.splits p).eq_prod_roots (fun w hw => by
      rw [inv_mul_eq_div, one_le_div hD]; exact hsep w hw)
  have hn₁ : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hfac : (p.roots.card : ℝ)*(p.roots.card-1) ≤ (n:ℝ)*(n-1) := by
    by_cases he : p.roots.card = 0
    · simp only [he, Nat.cast_zero, zero_mul]
      exact mul_nonneg (by positivity) (sub_nonneg.mpr hn₁)
    · have hk : (1:ℝ) ≤ p.roots.card := by exact_mod_cast (show 1 ≤ p.roots.card by omega)
      gcongr
  have hfirst : ‖p.derivative.eval z/p.eval z‖ ≤ (n:ℝ)/clearance := by
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hp), div_eq_mul_inv]
    grw [h₁, hcard]
  have hsecond : ‖p.derivative.derivative.eval z/p.eval z‖ ≤ (n:ℝ)*(n-1)/clearance^2 := by
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hp), div_eq_mul_inv, ← inv_pow]
    grw [h₂, hfac]
  have hn' : (80:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n:ℝ) := by linarith
  refine ⟨hsep, hz', hfirst, hsecond, ?_, ?_⟩
  · let d := p.derivative.eval z/p.eval z
    let e := p.derivative.derivative.eval z/p.eval z
    have hid : (removeMode n p).eval z/p.eval z = 1 + (e/2-z*d)/(n:ℂ) := by
      simp only [removeMode, EStar, eval_add, eval_mul, eval_sub, eval_C, eval_X, d, e]
      field_simp [hp]
    rw [hid]
    calc
      _ ≤ 1 + (‖e‖/2 + ‖z‖*‖d‖)/(n:ℝ) := by
        grw [norm_add_le, norm_div, norm_sub_le, norm_div, norm_mul]
        simp
      _ ≤ 1 + (((n:ℝ)*(n-1)/clearance^2)/2 + 1.15*((n:ℝ)/clearance))/(n:ℝ) := by gcongr
      _ = _ := by field_simp; ring
  · norm_num [clearance, div_eq_mul_inv]
    linarith only [hn']

private theorem G_eval (n : ℕ) (a z : ℂ) :
    (G n a).eval z = 1+2*z+a*psi n z := by
  simp [G, eval_add, eval_mul, Giroux.mode_eval]

private theorem G_degree (n : ℕ) (hn : 1 ≤ n) (a : ℂ) : (G n a).natDegree ≤ n := by
  have hm : (Giroux.mode n).natDegree ≤ n := (natDegree_C_mul_le ..).trans (hermite_degree n).1.le
  apply (natDegree_add_le ..).trans (max_le ?_ ((natDegree_C_mul_le ..).trans hm))
  apply (natDegree_add_le ..).trans (max_le (by simp) ?_)
  simpa using hn

private theorem remove_G (n : ℕ) (hn : 0 < n) (a z : ℂ) :
    (removeMode n (G n a)).eval z = 1+2*(1-1/(n:ℂ))*z := by
  have he := congrArg (eval z) (hermite_equation n)
  simp only [eval_sub, eval_neg, eval_mul, eval_natCast, eval_X, eval_ofNat,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] at he
  have hn' : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [removeMode, EStar, G, Giroux.mode, derivative_add, derivative_mul,
    eval_add, eval_sub, eval_mul]
  field_simp [hn']
  linear_combination (a*(Giroux.scale n : ℂ)⁻¹)*he

theorem affine_quotient (n : ℕ) (hn : 80 ≤ n) (a z : ℂ) (hz : z ∈ sphere (w₀:ℂ) R) :
    let g := (removeMode n (G n a)).eval z
    g = 1 + 2*(1-1/(n:ℂ))*z ∧
    1.3*(1-1/(n:ℝ)) - 1/(n:ℝ) ≤ ‖g‖ ∧ g ≠ 0 ∧
    ‖(1+2*z)/g‖ ≤ R/(R*(1-1/(n:ℝ))-1/(2*(n:ℝ))) ∧
    R/(R*(1-1/(n:ℝ))-1/(2*(n:ℝ))) ≤ R/0.635625 ∧ R/0.635625 < 1.03 := by
  dsimp only
  rw [remove_G n (by omega)]
  have hn' : (80:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  have hinv : 1/(n:ℝ) ≤ 1/80 := one_div_le_one_div_of_le (by norm_num) hn'
  let d : ℝ := R*(1-1/(n:ℝ))-1/(2*(n:ℝ))
  have hhalf : 1/(2*(n:ℝ)) = (1/(n:ℝ))/2 := by ring
  have hd : 0.635625 ≤ d := by dsimp [d, R]; rw [hhalf]; norm_num at hinv ⊢; linarith only [hinv]
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hlin : ‖1+2*z‖ = 1.3 := by
    rw [show 1+2*z = 2*(z-(w₀:ℂ)) by dsimp [w₀]; push_cast; ring,
      norm_mul, ← dist_eq_norm, mem_sphere.mp hz]
    norm_num [R]
  let L := 1+2*(1-1/(n:ℂ))*z
  have hid : ((1-1/(n:ℝ):ℝ):ℂ)*(1+2*z) = L - ((1/(n:ℝ):ℝ):ℂ) := by
    dsimp [L]; push_cast; ring
  have hlower : 1.3*(1-1/(n:ℝ))-1/(n:ℝ) ≤ ‖L‖ := by
    have hh := norm_sub_le L ((1/(n:ℝ):ℝ):ℂ)
    rw [← hid, norm_mul, hlin, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ 1-1/(n:ℝ)), abs_of_pos (by positivity : 0 < 1/(n:ℝ))] at hh
    linarith
  have htwo : 2*d ≤ ‖L‖ := by dsimp [d,R]; rw [hhalf]; norm_num at hlower ⊢; linarith only [hlower]
  have hnL := (mul_pos (by norm_num : (0:ℝ)<2) hdpos).trans_le htwo
  refine ⟨rfl, hlower, norm_pos_iff.mp hnL, ?_, ?_, by norm_num [R]⟩
  · rw [norm_div, hlin]
    change 1.3 / ‖L‖ ≤ R / d
    apply (div_le_div_iff₀ hnL hdpos).mpr
    dsimp [R]; linarith
  · exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd

theorem reciprocal_ratios (n : ℕ) (hn : 80 ≤ n) (a z : ℂ) (ha : a ≠ 0)
    (hz : z ∈ sphere (w₀:ℂ) R)
    (hlocal : ∀ b : ℂ, b = a ∨ b = conj a →
      ∀ w ∈ ball z clearance, (G n b).eval w ≠ 0) :
    ∀ b : ℂ, b = a ∨ b = conj a →
      let g := (G n b).eval z
      let Lg := (removeMode n (G n b)).eval z
      ‖(G n (conj b)).eval z / g‖ ≤ 1+2*‖(1+2*z)/Lg‖*‖Lg/g‖ ∧
      1+2*‖(1+2*z)/Lg‖*‖Lg/g‖ < 1+2*1.03*43*(n:ℝ) ∧
      1+2*1.03*43*(n:ℝ) < 90*(n:ℝ) := by
  intro b hb
  have hb' : b ≠ 0 := by rcases hb with rfl | rfl <;> simpa using ha
  have hg := hlocal b hb z (mem_ball_self (by norm_num : 0 < clearance))
  let g := (G n b).eval z
  let Lg := (removeMode n (G n b)).eval z
  let q := conj b / b
  have hq : ‖q‖ = 1 := by simp [q, hb']
  have hq' : ‖1-q‖ ≤ 2 := by have h := norm_sub_le (1:ℂ) q; rw [norm_one,hq] at h; linarith
  obtain ⟨_, _, hLg, h₁, h₂, h₃⟩ := affine_quotient n hn b z hz
  obtain ⟨_, _, _, _, h₄, h₅⟩ := boundary_derivatives _ n hn (G_degree n (by omega) b)
    z hz (hlocal b hb)
  have hid : (G n (conj b)).eval z/g = q+(1-q)*((1+2*z)/Lg)*(Lg/g) := by
    rw [mul_assoc, div_mul_div_cancel₀ hLg]
    rw [← mul_div_assoc, add_div' _ _ g hg]
    apply congrArg (· / g)
    dsimp [q, g]
    rw [G_eval, G_eval]
    field_simp [hb']; ring
  change ‖(G n (conj b)).eval z/g‖ ≤ _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [hid]
    grw [norm_add_le, norm_mul, norm_mul, hq, hq']
  · have hx := (h₁.trans h₂).trans_lt h₃
    have hy := h₄.trans_lt h₅
    have hn' : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    change 1+2*‖(1+2*z)/Lg‖*‖Lg/g‖ < _
    calc
      _ ≤ 1+2*1.03*‖Lg/g‖ := by gcongr
      _ < _ := by linarith only [hy]
  · have hn' : (80:ℝ) ≤ n := by exact_mod_cast hn
    norm_num
    linarith

/-- Normalize a primitive of p′/p at the center, then show p exp(−L) is constant. -/
private theorem disk_log (center : ℂ) (radius : ℝ) (hr : 0 < radius) (p : Polynomial ℂ) (hfree : ∀ v ∈ ball center radius, p.eval v ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball center radius) ∧
      ∀ v ∈ ball center radius, Complex.exp (L v) = p.eval v := by
  have hc : center ∈ ball center radius := mem_ball_self hr
  have hd := p.derivative.differentiable.differentiableOn.div p.differentiable.differentiableOn hfree
  obtain ⟨L, hL₀, hL⟩ := hd.isExactOn_ball.with_val_at center (Complex.log (p.eval center))
  refine ⟨L, fun v hv => (hL v hv).differentiableAt.differentiableWithinAt, ?_⟩
  let F (v : ℂ) := p.eval v * Complex.exp (-L v)
  have hF (v) (hv : v ∈ ball center radius) : HasDerivAt F 0 v := by
    apply ((p.hasDerivAt v).mul (hL v hv).neg.cexp).congr_deriv
    change _ * _ + _ * (_ * -(p.derivative.eval v / p.eval v)) = 0
    field_simp [hfree v hv]; ring
  intro v hv
  have heq := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball center radius).isPreconnected
    (fun w hw => (hF w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hF w hw).deriv) hv hc
  change p.eval v * Complex.exp (-L v) = p.eval center * Complex.exp (-L center) at heq
  rw [hL₀, Complex.exp_neg, Complex.exp_neg, Complex.exp_log (hfree _ hc), mul_inv_cancel₀ (hfree _ hc),
    ← div_eq_mul_inv, div_eq_one_iff_eq (Complex.exp_ne_zero _)] at heq
  exact heq.symm

private theorem conj_mem {z : ℂ} {r : ℝ} (hz : z ∈ ball (w₀:ℂ) r) :
    conj z ∈ ball (w₀:ℂ) r := by
  rwa [mem_ball, ← Complex.conj_ofReal w₀, Complex.dist_conj_conj]

theorem outer_log (p : Polynomial ℂ)
    (hfree : ∀ z ∈ ball (w₀:ℂ) outerRadius, p.eval z ≠ 0) :
    ∃ L : ℂ → ℂ, LogOn L (fun z => p.eval z) (ball (w₀:ℂ) outerRadius) ∧
      LogOn (fun z => L z - conj (L (conj z))) (fun z => p.eval z / reflectedValue p z)
        (ball (w₀:ℂ) outerRadius) := by
  obtain ⟨L,hL,he⟩ := disk_log _ _ (by norm_num : 0 < outerRadius) p hfree
  have hc : DifferentiableOn ℂ (fun z => conj (L (conj z))) (ball (w₀:ℂ) outerRadius) := by
    intro z hz
    have hd := (hL.differentiableAt (isOpen_ball.mem_nhds (conj_mem hz))).conj_conj
    simpa only [Complex.conj_conj, Function.comp_def] using hd.differentiableWithinAt
  exact ⟨L, ⟨hL.analyticOnNhd isOpen_ball, he⟩, (hL.sub hc).analyticOnNhd isOpen_ball,
    fun z hz => by rw [Complex.exp_sub, Complex.exp_conj, he z hz, he _ (conj_mem hz)]; rfl⟩

private theorem inner_subset : closedBall (w₀:ℂ) R ⊆ ball (w₀:ℂ) outerRadius :=
  closedBall_subset_ball (by norm_num)

private theorem boundary_max {g : ℂ → ℂ} {C : ℝ}
    (hg : DifferentiableOn ℂ g (ball (w₀:ℂ) outerRadius))
    (hb : ∀ z ∈ sphere (w₀:ℂ) R, ‖g z‖ < C) :
    ∀ z ∈ closedBall (w₀:ℂ) R, ‖g z‖ < C := by
  obtain ⟨w, hw, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm isBounded_ball
    (nonempty_ball.mpr (by norm_num : 0 < R)) (hg.diffContOnCl_ball inner_subset)
  intro z hz
  exact (hmax (by rwa [closure_ball (w₀:ℂ) (by norm_num : R ≠ 0)])).trans_lt
    (hb w (frontier_ball_subset_sphere hw))

theorem closed_log_bound (p : Polynomial ℂ) (n : ℕ) (hn : 80 ≤ n) (f : ℂ → ℂ)
    (hf : LogOn f (fun z => p.eval z / reflectedValue p z) (ball (w₀:ℂ) outerRadius))
    (hbd : ∀ z ∈ sphere (w₀:ℂ) R, ‖p.eval z / reflectedValue p z‖ < 90*n ∧
      ‖reflectedValue p z / p.eval z‖ < 90*n) :
    InnerProductSpace.HarmonicOnNhd (fun z => (f z).re) (ball (w₀:ℂ) outerRadius) ∧
    ∀ z ∈ closedBall (w₀:ℂ) R, (f z).re = Real.log ‖p.eval z / reflectedValue p z‖ ∧
      |(f z).re| < logBound n := by
  have hd := hf.1.differentiableOn
  have hup := boundary_max hd.cexp (fun z hz => by
    rw [hf.2 z (inner_subset (sphere_subset_closedBall hz))]
    exact (hbd z hz).1)
  have hlo := boundary_max hd.neg.cexp (C := 90*(n:ℝ)) (fun z hz => by
    rw [Pi.neg_apply, Complex.exp_neg, hf.2 z (inner_subset (sphere_subset_closedBall hz)), inv_div]
    exact (hbd z hz).2)
  refine ⟨fun z hz => (hf.1 z hz).harmonicAt_re, ?_⟩
  intro z hz
  have h : Complex.exp (f z) = p.eval z / reflectedValue p z := hf.2 z (inner_subset hz)
  have hpos : 0 < 90*(n:ℝ) := by exact_mod_cast (show 0 < 90*n by omega)
  refine ⟨by rw [← h, Complex.norm_exp, Real.log_exp], abs_lt.mpr ⟨?_, ?_⟩⟩
  · have hh := hlo z hz
    simp only [Pi.neg_apply, Complex.norm_exp, Complex.neg_re] at hh
    have := (Real.lt_log_iff_exp_lt hpos).mpr hh
    dsimp [logBound]; linarith
  · exact (Real.lt_log_iff_exp_lt hpos).mpr (by simpa only [Complex.norm_exp] using hup z hz)

private theorem diameter_mem {t : ℝ} (ht : t ∈ diameter) : (t:ℂ) ∈ ball (w₀:ℂ) R := by
  rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/-- Two continuous argument lifts differ by a constant on a connected set. -/
private theorem phase_difference {p : Polynomial ℂ} {S : Set ℝ} {θ η : ℝ → ℝ}
    (hS : IsPreconnected S) (hθ : PhaseOn θ p S) (hη : PhaseOn η p S)
    {s t : ℝ} (hs : s ∈ S) (ht : t ∈ S) : θ s-η s = θ t-η t := by
  apply (AddCircle.isCoveringMap_coe (2*Real.pi)).constOn_of_comp hS (hθ.1.sub hη.1) _ hs ht
  intro x hx y hy
  change ((θ x-η x : ℝ) : Real.Angle) = ((θ y-η y : ℝ) : Real.Angle)
  simp only [Real.Angle.coe_sub, (hθ.2 x hx).2, (hη.2 x hx).2, (hθ.2 y hy).2,
    (hη.2 y hy).2, sub_self]

theorem diameter_derivative (p : Polynomial ℂ) (f : ℂ → ℂ)
    (hf : LogOn f (fun z => p.eval z / reflectedValue p z) (ball (w₀:ℂ) outerRadius)) :
    (∃ θ : ℝ → ℝ, PhaseOn θ p diameter) ∧
    ∀ θ : ℝ → ℝ, PhaseOn θ p diameter → ∀ t ∈ diameter,
      HasDerivAt θ (p.derivative.eval (t:ℂ) / p.eval (t:ℂ)).im t ∧
      (f (t:ℂ)).re = 0 ∧ deriv f (t:ℂ) = 2*Complex.I*((deriv θ t : ℝ) : ℂ) := by
  let U := ball (w₀:ℂ) outerRadius
  have hfree (z : ℂ) (hz : z ∈ U) : p.eval z ≠ 0 := by
    have hn := Complex.exp_ne_zero (f z)
    rw [hf.2 z hz] at hn
    exact fun he => hn (by simp [he])
  obtain ⟨L,hL,_⟩ := outer_log p hfree
  let η (s : ℝ) := (L (s:ℂ)).im
  have hmem (s : ℝ) (hs : s ∈ diameter) := inner_subset (ball_subset_closedBall (diameter_mem hs))
  have hη : PhaseOn η p diameter := by
    refine ⟨Complex.continuous_im.comp_continuousOn
      (hL.1.continuousOn.comp Complex.continuous_ofReal.continuousOn hmem), ?_⟩
    intro s hs
    refine ⟨hfree _ (hmem s hs), ?_⟩
    have he : Complex.exp (L (s:ℂ)) = p.eval (s:ℂ) := hL.2 _ (hmem s hs)
    rw [← he, Complex.arg_exp, Real.Angle.coe_toIocMod]
  refine ⟨⟨η,hη⟩, ?_⟩
  intro θ hθ t ht
  have hu := hmem t ht
  have hp := hfree _ hu
  let u := p.eval (t:ℂ)
  let v := p.derivative.eval (t:ℂ)
  let d := v/u
  have hLc := (hL.1 _ hu).differentiableAt
  have heq := ((hLc.hasDerivAt.cexp).congr_of_eventuallyEq
    (isOpen_ball.eventually_mem hu |>.mono fun x hx => (hL.2 x hx).symm)).deriv
  rw [(p.hasDerivAt (t:ℂ)).deriv, hL.2 _ hu] at heq
  have hderL : HasDerivAt L d (t:ℂ) := hLc.hasDerivAt.congr_deriv (by
    change _ = v/u
    apply (eq_div_iff hp).mpr
    simpa [u,v,mul_comm] using heq.symm)
  have hη' : HasDerivAt η d.im t := by
    simpa [η,mul_neg,Complex.mul_I_re] using (hderL.mul_const (-Complex.I)).real_of_complex
  have hθ' : HasDerivAt θ d.im t := (hη'.add_const (θ t-η t)).congr_of_eventuallyEq (by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    have := phase_difference isPreconnected_Ioo hθ hη hx ht
    linarith)
  have hr : HasDerivAt (reflectedValue p) (conj v) (t:ℂ) := by
    change HasDerivAt (fun w => conj (p.eval (conj w))) (conj v) (t:ℂ)
    simpa only [Complex.conj_ofReal, Function.comp_def, v] using!
      (p.hasDerivAt (t:ℂ)).conj_conj
  have hv : reflectedValue p (t:ℂ) = conj u := by simp only [reflectedValue, Complex.conj_ofReal, u]
  have hcu : conj u ≠ 0 := by simpa [u] using hp
  have hfval : Complex.exp (f (t:ℂ)) = u/conj u := (hf.2 _ hu).trans (by change u/reflectedValue p (t:ℂ) = _; rw [hv])
  have hnorm := congrArg norm hfval
  rw [Complex.norm_exp, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hp)] at hnorm
  refine ⟨hθ', by simpa using hnorm, ?_⟩
  have hfd := (hf.1 _ hu).differentiableAt.hasDerivAt.cexp
  have hdq := (p.hasDerivAt (t:ℂ)).div hr (hv ▸ hcu)
  have hder := (hfd.congr_of_eventuallyEq
    (isOpen_ball.eventually_mem hu |>.mono fun x hx => (hf.2 x hx).symm)).unique hdq
  rw [hfval, hv] at hder
  have hdiff : deriv f (t:ℂ) = d-conj d := by
    have hu₀ : u ≠ 0 := hp
    calc
      _ = ((v*conj u-u*conj v)/(conj u)^2)/(u/conj u) := by
        apply (eq_div_iff (div_ne_zero hu₀ hcu)).mpr
        simpa only [mul_comm (deriv f (t:ℂ))] using hder
      _ = _ := by dsimp only [d]; rw [map_div₀]; field_simp [hu₀,hcu]
  rw [hθ'.deriv, hdiff]
  apply Complex.ext <;> simp [Complex.mul_im, Complex.mul_re]
  ring


private theorem logBound_pos {n : ℕ} (hn : 80 ≤ n) : 0 < logBound n := by
  apply Real.log_pos
  have hn' : (80:ℝ) ≤ n := by exact_mod_cast hn
  linarith

private theorem tan_disk {z : ℂ} (hz : |z.re| < Real.pi/4) :
    Complex.cos z ≠ 0 ∧ ‖Complex.tan z‖ < 1 := by
  have hcos := Real.cos_pos_of_mem_Ioo (x := 2*z.re)
    ⟨by linarith [(abs_lt.mp hz).1], by linarith [(abs_lt.mp hz).2]⟩
  have hdiff : ‖Complex.cos z‖^2-‖Complex.sin z‖^2 = Real.cos (2*z.re) := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.cos_eq z, Complex.sin_eq z, Real.cos_two_mul']
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im]
    simp only [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.sinh_ofReal_re]
    linear_combination (Real.cos z.re^2-Real.sin z.re^2)*Real.cosh_sq_sub_sinh_sq z.im
  have hlt : ‖Complex.sin z‖ < ‖Complex.cos z‖ :=
    (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith only [hdiff, hcos])
  have hpos := (norm_nonneg _).trans_lt hlt
  exact ⟨norm_pos_iff.mp hpos, by rw [Complex.tan_eq_sin_div_cos, norm_div, div_lt_one hpos]; exact hlt⟩

private theorem normalized_eq (n : ℕ) (f : ℂ → ℂ) (t : ℝ) :
    normalizedLog n f t = fun z => ((Real.pi/(4*logBound n):ℝ):ℂ)*(f z-f (t:ℂ)) := by
  funext z; dsimp [normalizedLog]; push_cast; ring

theorem tangent_normalization (n : ℕ) (hn : 80 ≤ n) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball (w₀:ℂ) R))
    (hstrip : ∀ z ∈ ball (w₀:ℂ) R, |(f z).re| < logBound n)
    (t : ℝ) (ht : t ∈ diameter) (hreal : (f (t:ℂ)).re = 0) :
    let F := normalizedLog n f t
    (∀ z ∈ ball (w₀:ℂ) R, |(F z).re| < Real.pi/4) ∧
    DifferentiableOn ℂ (Complex.tan ∘ F) (ball (w₀:ℂ) R) ∧
    MapsTo (Complex.tan ∘ F) (ball (w₀:ℂ) R) (ball 0 1) ∧
    (Complex.tan ∘ F) (t:ℂ) = 0 ∧ deriv (Complex.tan ∘ F) (t:ℂ) = deriv F (t:ℂ) := by
  let k := Real.pi/(4*logBound n)
  have hk : 0 < k := div_pos Real.pi_pos (mul_pos (by norm_num) (logBound_pos hn))
  let F := normalizedLog n f t
  have hF : DifferentiableOn ℂ F (ball (w₀:ℂ) R) := by
    rw [show F = _ from normalized_eq ..]
    exact (hf.sub_const _).const_mul _
  have hFs (z) (hz : z ∈ ball (w₀:ℂ) R) : |(F z).re| < Real.pi/4 := by
    rw [show F = _ from normalized_eq .., Complex.re_ofReal_mul, Complex.sub_re, hreal, sub_zero,
      abs_mul, abs_of_pos hk]
    calc
      _ < k*logBound n := mul_lt_mul_of_pos_left (hstrip z hz) hk
      _ = _ := by dsimp [k]; field_simp [(logBound_pos hn).ne']
  have hFt : F (t:ℂ) = 0 := by simp [F, normalizedLog]
  have hFt' := hF.differentiableAt (isOpen_ball.mem_nhds (diameter_mem ht))
  have htand := (Complex.hasDerivAt_tan (by rw [hFt]; simp)).comp (t:ℂ) hFt'.hasDerivAt
  refine ⟨hFs, fun z hz => ((Complex.hasDerivAt_tan (tan_disk (hFs z hz)).1).differentiableAt.comp
    z (hF.differentiableAt (isOpen_ball.mem_nhds hz))).differentiableWithinAt,
    fun z hz => mem_ball_zero_iff.mpr (tan_disk (hFs z hz)).2, ?_, ?_⟩
  · change Complex.tan (F (t:ℂ)) = 0
    rw [hFt, Complex.tan_zero]
  · simpa [hFt] using htand.deriv

theorem schwarz_pick_at_real (H : ℂ → ℂ) (hH : DifferentiableOn ℂ H (ball (w₀:ℂ) R))
    (hm : MapsTo H (ball (w₀:ℂ) R) (ball 0 1)) (t : ℝ) (ht : t ∈ diameter)
    (hzero : H (t:ℂ) = 0) : ‖deriv H (t:ℂ)‖ ≤ R/(R^2-(t-w₀)^2) := by
  let a : ℝ := (t-w₀)/R
  have hR : 0 < R := by norm_num
  have ha : |a| < 1 := by
    rw [abs_div, abs_of_pos hR, div_lt_one hR, abs_lt]
    constructor <;> linarith [ht.1,ht.2]
  have ha₂ : 0 < 1-a^2 := by
    nlinarith only [mul_pos (by linarith [(abs_lt.mp ha).1] : 0 < 1+a) (by linarith [(abs_lt.mp ha).2] : 0 < 1-a)]
  -- This automorphism sends 0 to a. The identity of squared norms proves
  -- that it preserves the open unit disk.
  let B (w : ℂ) := (w+(a:ℂ))/(1+(a:ℂ)*w)
  let φ (w : ℂ) := (w₀:ℂ)+(R:ℂ)*B w
  have hlt (w : ℂ) (hw : w ∈ ball (0:ℂ) 1) : ‖w+(a:ℂ)‖ < ‖1+(a:ℂ)*w‖ := by
    have hw₂ : 0 < 1-‖w‖^2 := by
      nlinarith only [(sq_lt_sq₀ (norm_nonneg w) zero_le_one).mpr (mem_ball_zero_iff.mp hw)]
    have hid : ‖1+(a:ℂ)*w‖^2 - ‖w+(a:ℂ)‖^2 = (1-a^2)*(1-‖w‖^2) := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.ofReal_re, Complex.ofReal_im,
        Complex.one_re, Complex.one_im]
      ring
    exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith only [hid,mul_pos ha₂ hw₂])
  have hden (w : ℂ) (hw : w ∈ ball (0:ℂ) 1) := norm_pos_iff.mp ((norm_nonneg _).trans_lt (hlt w hw))
  have hmap : MapsTo φ (ball 0 1) (ball (w₀:ℂ) R) := by
    intro w hw
    change dist ((w₀:ℂ)+(R:ℂ)*B w) (w₀:ℂ) < R
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    apply mul_lt_of_lt_one_right hR
    dsimp only [B]
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (hden w hw))]
    exact hlt w hw
  have hB : DifferentiableOn ℂ B (ball 0 1) :=
    (differentiableOn_id.add_const _).div (differentiableOn_id.const_mul _ |>.const_add 1) hden
  have hφ : DifferentiableOn ℂ φ (ball 0 1) := (hB.const_mul _).const_add _
  have hφ₀ : φ 0 = (t:ℂ) := by
    simp only [φ, B, zero_add, mul_zero, add_zero, div_one]; dsimp [a]; push_cast; ring
  have dB : HasDerivAt B (1-(a:ℂ)^2) 0 := by
    apply (((hasDerivAt_id (0:ℂ)).add_const (a:ℂ)).div
      (((hasDerivAt_id (0:ℂ)).const_mul (a:ℂ)).const_add 1) (by simp)).congr_deriv
    simp only [id_eq, zero_add, mul_zero, add_zero, mul_one, one_pow, div_one]
    ring
  have dφ := (dB.const_mul (R:ℂ)).const_add (w₀:ℂ)
  have dH := (hH.differentiableAt (isOpen_ball.mem_nhds (diameter_mem ht))).hasDerivAt
  have hd := (hφ₀.symm ▸ dH : HasDerivAt H (deriv H (t:ℂ)) (φ 0)).comp 0 dφ
  change HasDerivAt (H ∘ φ) (deriv H (t:ℂ)*((R:ℂ)*(1-(a:ℂ)^2))) 0 at hd
  have hcenter : (H ∘ φ) 0 = 0 := by simp [hφ₀,hzero]
  have hh := Complex.norm_deriv_le_div_of_mapsTo_ball (hH.comp hφ hmap)
    (R₂ := 1) (fun z hz => by rw [hcenter]; exact ball_subset_closedBall (hm (hmap hz))) zero_lt_one
  rw [hd.deriv, norm_mul, show (R:ℂ)*(1-(a:ℂ)^2) = ((R*(1-a^2):ℝ):ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hR ha₂), div_one] at hh
  have hscale : R^2-(t-w₀)^2 = R * (R*(1-a^2)) := by dsimp [a]; field_simp
  rw [hscale, div_mul_eq_div_div, div_self hR.ne', le_div_iff₀ (mul_pos hR ha₂)]
  exact hh

theorem phase_derivative_bound (n : ℕ) (hn : 80 ≤ n) (p : Polynomial ℂ) (f : ℂ → ℂ)
    (hf : LogOn f (fun z => p.eval z / reflectedValue p z) (ball (w₀:ℂ) outerRadius))
    (hstrip : ∀ z ∈ ball (w₀:ℂ) R, |(f z).re| < logBound n)
    (θ : ℝ → ℝ) (hθ : PhaseOn θ p diameter) (t : ℝ) (ht : t ∈ diameter) :
    ‖deriv (normalizedLog n f t) (t:ℂ)‖ ≤ R/(R^2-(t-w₀)^2) ∧
    |deriv θ t| ≤ (2*logBound n/Real.pi)*R/(R^2-(t-w₀)^2) := by
  obtain ⟨_, hreal, hphase⟩ := (diameter_derivative p f hf).2 θ hθ t ht
  have hd := hf.1.differentiableOn.mono (ball_subset_ball (by norm_num : R ≤ outerRadius))
  obtain ⟨_,hT,hm,hzero,hder⟩ := tangent_normalization n hn f hd hstrip t ht hreal
  have h := schwarz_pick_at_real _ hT hm t ht hzero
  rw [hder] at h
  refine ⟨h, ?_⟩
  let k := Real.pi/(4*logBound n)
  have hk : 0 < k := div_pos Real.pi_pos (mul_pos (by norm_num) (logBound_pos hn))
  have hdf := (hd.differentiableAt (isOpen_ball.mem_nhds (diameter_mem ht))).hasDerivAt
  have he : deriv (normalizedLog n f t) (t:ℂ) = (k:ℂ)*deriv f (t:ℂ) := by
    rw [normalized_eq]; exact ((hdf.sub_const _).const_mul _).deriv
  rw [he, hphase] at h
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk,
    Complex.norm_ofNat, Complex.norm_I, mul_one] at h
  have hconst : (2*logBound n/Real.pi)*(k*2) = 1 := by
    dsimp [k]; field_simp [(logBound_pos hn).ne', Real.pi_ne_zero]; ring
  have hcoef : 0 ≤ 2*logBound n/Real.pi := div_nonneg (mul_nonneg (by norm_num) (logBound_pos hn).le) Real.pi_pos.le
  calc
    _ = (2*logBound n/Real.pi)*(k*(2*|deriv θ t|)) := by linear_combination -(abs (deriv θ t)) * hconst
    _ ≤ _ := by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left h hcoef


theorem consecutive_nodes (n : ℕ) (hn : 80 ≤ n) (hcenter : psi n (w₀:ℂ) ≠ 0) :
    ∃ s₁ s₂ : ℝ,
      IsGreatest {s : ℝ | s ∈ Icc (w₀-beta n) w₀ ∧ psi n (s:ℂ) = 0} s₁ ∧
      IsLeast {s : ℝ | s ∈ Icc w₀ (w₀+beta n) ∧ psi n (s:ℂ) = 0} s₂ ∧
      s₁ < w₀ ∧ w₀ < s₂ ∧ (∀ s ∈ Ioo s₁ s₂, psi n (s:ℂ) ≠ 0) ∧ s₂-s₁ < beta n := by
  let k := Real.sqrt (2*(n:ℝ))
  have hn' : (80:ℝ) ≤ n := by exact_mod_cast hn
  have hk : 0 < k := Real.sqrt_pos.mpr (by positivity)
  have hk₂ : k^2 = 2*(n:ℝ) := Real.sq_sqrt (by positivity)
  have hkmin : 63/5 ≤ k := by
    apply (sq_le_sq₀ (by norm_num) hk.le).mp
    nlinarith only [hk₂, hn']
  let b := beta n
  have hβ : b < 1/4 := (div_lt_iff₀ hk).mpr (by linarith [Real.pi_lt_d2])
  have hb : 0 < b := div_pos Real.pi_pos hk
  have hit (u : ℝ) (hu : w₀-b ≤ u) (hu' : u ≤ w₀) : ∃ v ∈ Ioo u (u+b), psi n v = 0 := by
    apply hermite_sturm_interval n u k hk
    intro v hv
    change u < v ∧ v < u+b at hv
    have h₁ : -1 < v := by dsimp only [w₀] at hu; linarith [hv.1]
    have h₂ : v < 1 := by dsimp only [w₀] at hu'; linarith [hv.2]
    nlinarith only [hk₂, mul_pos (by linarith : 0 < v+1) (by linarith : 0 < 1-v)]
  let S (l r : ℝ) := {x : ℝ | x ∈ Icc l r ∧ psi n x = 0}
  have compact (l r : ℝ) : IsCompact (S l r) :=
    isCompact_Icc.inter_right (isClosed_eq (((hermite n).continuous.div_const _).comp Complex.continuous_ofReal)
      continuous_const)
  obtain ⟨u, hu, hpu⟩ := hit (w₀-b) le_rfl (by linarith)
  have hleft : (S (w₀-b) w₀).Nonempty := ⟨u, ⟨hu.1.le, by linarith [hu.2]⟩, hpu⟩
  obtain ⟨s, hsg⟩ := (compact _ _).exists_isGreatest hleft
  obtain ⟨hs,hmax⟩ := hsg
  obtain ⟨v, hv, hpv⟩ := hit s hs.1.1 hs.1.2
  have hvc : w₀ < v := by
    by_contra! h
    exact hv.1.not_ge (hmax (show v ∈ S (w₀-b) w₀ from ⟨⟨hs.1.1.trans hv.1.le,h⟩,hpv⟩))
  have hvS : v ∈ S w₀ (w₀+b) := ⟨⟨hvc.le, by linarith [hv.2,hs.1.2]⟩,hpv⟩
  obtain ⟨t, htl⟩ := (compact _ _).exists_isLeast ⟨v,hvS⟩
  obtain ⟨ht,hmin⟩ := htl
  have hs' : s < w₀ := lt_of_le_of_ne hs.1.2 (fun e => hcenter (by simpa only [← e] using hs.2))
  have ht' : w₀ < t := lt_of_le_of_ne ht.1.1 (fun e => hcenter (by simpa only [e] using ht.2))
  refine ⟨s,t, ⟨hs,fun _ hx => hmax hx⟩, ⟨ht,fun _ hx => hmin hx⟩,hs',ht',?_,?_⟩
  · intro x hx hzero
    rcases le_total x w₀ with hc | hc
    · exact hx.1.not_ge (hmax (show x ∈ S (w₀-b) w₀ from ⟨⟨hs.1.1.trans hx.1.le,hc⟩,hzero⟩))
    · exact hx.2.not_ge (hmin (show x ∈ S w₀ (w₀+b) from ⟨⟨hc,hx.2.le.trans ht.1.2⟩,hzero⟩))
  · have htv : t ≤ v := hmin hvS
    change t-s < b
    linarith [hv.2]

private theorem psi_real_im (n : ℕ) (x : ℝ) : (psi n (x:ℂ)).im = 0 := by
  have h : ((hermite n).eval (x:ℂ)).im = 0 := by
    apply Complex.conj_eq_iff_im.mp; simpa using (hermite_symmetry n (x:ℂ)).1.symm
  simp only [psi, Complex.div_ofReal_im, h, zero_div]

private theorem G_im (n : ℕ) (a : ℂ) (x : ℝ) :
    ((G n a).eval (x:ℂ)).im = a.im*(psi n (x:ℂ)).re := by
  simp [G_eval, Complex.add_im, Complex.mul_im, psi_real_im]

private theorem G_at_node {n : ℕ} (a : ℂ) {s : ℝ} (hs : psi n (s:ℂ) = 0) :
    (G n a).eval (s:ℂ) = ((1+2*s : ℝ):ℂ) := by simp [G_eval,hs]

theorem real_coefficient_zero (n : ℕ) (a s₁ s₂ : ℝ) (hs₁ : s₁ < w₀) (hs₂ : w₀ < s₂)
    (h₁ : psi n (s₁:ℂ) = 0) (h₂ : psi n (s₂:ℂ) = 0) :
    ∃ t ∈ Ioo s₁ s₂, (G n (a:ℂ)).eval (t:ℂ) = 0 := by
  let p := G n (a:ℂ)
  have hneg : (p.eval (s₁:ℂ)).re < 0 := by rw [G_at_node _ h₁]; dsimp [w₀] at hs₁; simpa using (by linarith : 1+2*s₁ < 0)
  have hpos : 0 < (p.eval (s₂:ℂ)).re := by rw [G_at_node _ h₂]; dsimp [w₀] at hs₂; simpa using (by linarith : 0 < 1+2*s₂)
  obtain ⟨t, ht, he⟩ := intermediate_value_Ioo (hs₁.trans hs₂).le
    (Complex.continuous_re.comp (p.continuous.comp Complex.continuous_ofReal)).continuousOn ⟨hneg,hpos⟩
  exact ⟨t,ht,Complex.ext he (by simp [G_im])⟩

theorem exact_phase_change (n : ℕ) (a : ℂ) (ha : a.im ≠ 0) (s₁ s₂ : ℝ)
    (hs₁ : s₁ < w₀) (hs₂ : w₀ < s₂) (h₁ : psi n (s₁:ℂ) = 0) (h₂ : psi n (s₂:ℂ) = 0)
    (hinterior : ∀ t ∈ Ioo s₁ s₂, psi n (t:ℂ) ≠ 0) :
    (∀ t ∈ Ioo s₁ s₂, ((G n a).eval (t:ℂ)).im = a.im * (psi n (t:ℂ)).re) ∧
    ((∀ t ∈ Ioo s₁ s₂, 0 < ((G n a).eval (t:ℂ)).im) ∨
     (∀ t ∈ Ioo s₁ s₂, ((G n a).eval (t:ℂ)).im < 0)) ∧
    (∃ θ : ℝ → ℝ, PhaseOn θ (G n a) (Icc s₁ s₂)) ∧
    ∀ θ : ℝ → ℝ, PhaseOn θ (G n a) (Icc s₁ s₂) → |θ s₂-θ s₁| = Real.pi := by
  let p := G n a
  let V (t : ℝ) := p.eval (t:ℂ)
  have hVc : Continuous V := p.continuous.comp Complex.continuous_ofReal
  have hnv (x : ℝ) (hx : x ∈ Ioo s₁ s₂) : (V x).im ≠ 0 := by
    rw [show (V x).im = _ from G_im n a x]
    apply mul_ne_zero ha
    intro he
    exact hinterior x hx (Complex.ext he (psi_real_im n x))
  have hsign : (∀ t ∈ Ioo s₁ s₂, 0 < (V t).im) ∨ (∀ t ∈ Ioo s₁ s₂, (V t).im < 0) := by
    by_cases hall : ∀ t ∈ Ioo s₁ s₂, 0 < (V t).im
    · exact Or.inl hall
    push Not at hall
    obtain ⟨u, hu, hneg⟩ := hall
    refine Or.inr (fun v hv => lt_of_not_ge (fun hpos => ?_))
    obtain ⟨x,hx,hzero⟩ := isPreconnected_Ioo.intermediate_value hu hv
      (Complex.continuous_im.comp hVc).continuousOn ⟨hneg,hpos⟩
    exact hnv x hx hzero
  -- Rotate the one-sided path into the slit plane. Its real endpoints then
  -- lie on opposite imaginary rays, with arguments ±π/2.
  obtain ⟨c,hc,hrot⟩ : ∃ c : ℂ, (c = Complex.I ∨ c = -Complex.I) ∧
      ∀ t ∈ Ioo s₁ s₂, 0 < (c*V t).re := by
    rcases hsign with hpos | hneg
    · exact ⟨-Complex.I, Or.inr rfl, fun t ht => by simpa using hpos t ht⟩
    · exact ⟨Complex.I, Or.inl rfl, fun t ht => by simpa using hneg t ht⟩
  have hc₀ : c ≠ 0 := by rcases hc with rfl | rfl <;> simp
  have hci : c.im ≠ 0 := by rcases hc with rfl | rfl <;> simp
  have hx₁ : 1+2*s₁ < 0 := by dsimp [w₀] at hs₁; linarith
  have hx₂ : 0 < 1+2*s₂ := by dsimp [w₀] at hs₂; linarith
  have hv₁ : V s₁ = ((1+2*s₁:ℝ):ℂ) := G_at_node _ h₁
  have hv₂ : V s₂ = ((1+2*s₂:ℝ):ℂ) := G_at_node _ h₂
  have hslit (x : ℝ) (hx : x ∈ Icc s₁ s₂) : c*V x ∈ Complex.slitPlane := by
    rcases eq_or_lt_of_le hx.1 with he | hleft
    · rw [← he,hv₁]; exact Or.inr (by simp [hci, hx₁.ne])
    rcases eq_or_lt_of_le hx.2 with he | hright
    · rw [he,hv₂]; exact Or.inr (by simp [hci, hx₂.ne'])
    exact Or.inl (hrot _ ⟨hleft,hright⟩)
  let η (x : ℝ) := (c*V x).arg-c.arg
  have hη : PhaseOn η p (Icc s₁ s₂) := by
    refine ⟨(Complex.continuousOn_arg.comp (continuous_const.mul hVc).continuousOn hslit).sub continuousOn_const, ?_⟩
    intro x hx
    have hn : V x ≠ 0 := fun he => Complex.zero_notMem_slitPlane (by simpa [he] using hslit x hx)
    refine ⟨hn,?_⟩
    change (((c*V x).arg-c.arg : ℝ):Real.Angle) = (V x).arg
    rw [Real.Angle.coe_sub,Complex.arg_mul_coe_angle hc₀ hn]; abel
  refine ⟨fun x _ => G_im n a x,hsign,⟨η,hη⟩,?_⟩
  intro θ hθ
  have he := phase_difference isPreconnected_Icc hθ hη (right_mem_Icc.mpr (hs₁.trans hs₂).le)
    (left_mem_Icc.mpr (hs₁.trans hs₂).le)
  rw [show θ s₂-θ s₁ = η s₂-η s₁ by linarith only [he]]
  simp only [η, hv₁,hv₂, sub_sub_sub_cancel_right, Complex.arg_mul_real hx₂]
  rw [show c*((1+2*s₁:ℝ):ℂ) = (-c)*((-(1+2*s₁):ℝ):ℂ) by push_cast; ring,
    Complex.arg_mul_real (neg_pos.mpr hx₁)]
  rcases hc with rfl | rfl <;> simp only [Complex.arg_I, Complex.arg_neg_I, neg_neg]
  · rw [show Real.pi/2 - -(Real.pi/2) = Real.pi by ring, abs_of_pos Real.pi_pos]
  · rw [show -(Real.pi/2) - Real.pi/2 = -Real.pi by ring, abs_neg, abs_of_pos Real.pi_pos]

private theorem artanh_derivative (x : ℝ) (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt Real.artanh (1/(1-x^2)) x := by
  have hp : 0 < 1+x := by linarith [hx.1]
  have hm : 0 < 1-x := sub_pos.mpr hx.2
  have hq := ((hasDerivAt_id x).const_add 1).div ((hasDerivAt_id x).const_sub 1) hm.ne'
  have hd := (hq.log (div_pos hp hm).ne').const_mul (1/2:ℝ)
  apply (hd.congr_of_eventuallyEq ?_).congr_deriv
  · dsimp; field_simp [hm.ne', hp.ne', show 1-x^2 ≠ 0 by nlinarith only [mul_pos hp hm]]
    ring
  · filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact Real.artanh_eq_half_log ⟨hy.1.le,hy.2.le⟩

private theorem scaled_derivative {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo (-r) r) :
    HasDerivAt (fun u : ℝ => Real.artanh (u/r)) (r/(r^2-x^2)) x := by
  have hu : x/r ∈ Ioo (-1:ℝ) 1 := ⟨(lt_div_iff₀ hr).mpr (by linarith [hx.1]),
    (div_lt_one hr).mpr hx.2⟩
  apply ((artanh_derivative _ hu).comp x ((hasDerivAt_id x).div_const r)).congr_deriv
  have hsq : 0 < r^2-x^2 := by
    nlinarith only [mul_pos (sub_pos.mpr hx.2) (by linarith [hx.1] : 0 < r+x)]
  field_simp [hr.ne',hsq.ne']

private theorem scaled_convex {r : ℝ} (hr : 0 < r) :
    StrictConvexOn ℝ (Ico 0 r) (fun x : ℝ => Real.artanh (x/r)) := by
  have hd (x : ℝ) (hx : x ∈ Ico 0 r) := scaled_derivative hr (show x ∈ Ioo (-r) r from
    ⟨by linarith [hx.1],hx.2⟩)
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ico ..)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
  intro x hx y hy hxy
  have hx' : x ∈ Ico 0 r := interior_subset hx
  have hy' : y ∈ Ico 0 r := interior_subset hy
  rw [(hd _ hx').deriv, (hd _ hy').deriv]
  apply div_lt_div_of_pos_left hr
  · nlinarith only [mul_pos (sub_pos.mpr hy'.2) (by linarith [hy'.1] : 0 < r+y)]
  · nlinarith only [sq_lt_sq₀ hx'.1 hy'.1 |>.mpr hxy]

theorem artanh_primitive :
    J 0 = 0 ∧ (∀ u ∈ Ioo (-R) R, HasDerivAt J (R/(R^2-u^2)) u) ∧
    ConvexOn ℝ (Ico 0 R) J ∧
    ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u+v < R → J u + J v ≤ J (u+v) := by
  have hR : 0 < R := by norm_num
  have h₀ : J 0 = 0 := by simp [J,Real.artanh_zero]
  have hconv : ConvexOn ℝ (Ico 0 R) J := (scaled_convex hR).convexOn
  refine ⟨h₀, fun _ hx => scaled_derivative hR hx, hconv, ?_⟩
  intro u v hu hv huv
  rcases hu.eq_or_lt with e | hu'
  · subst u; simp [h₀]
  rcases hv.eq_or_lt with e | hv'
  · subst v; simp [h₀]
  let s := u+v
  have hs : 0 < s := add_pos hu' hv'
  have bound (x : ℝ) (hx : 0 < x) (hxs : x ≤ s) : J x*s ≤ J s*x := by
    have h := hconv.secant_mono (show (0:ℝ) ∈ Ico 0 R from ⟨le_rfl,hR⟩)
      ⟨hx.le,hxs.trans_lt huv⟩ ⟨hs.le,huv⟩ hx.ne' hs.ne' hxs
    simpa only [h₀,sub_zero,div_le_div_iff₀ hx hs] using h
  apply (mul_le_mul_iff_of_pos_right hs).mp
  rw [add_mul]
  calc
    _ ≤ J s*u + J s*v := add_le_add (bound u hu' (by dsimp [s]; linarith))
      (bound v hv' (by dsimp [s]; linarith))
    _ = _ := by dsimp [s]; ring

private theorem J_neg {x : ℝ} (hx : x ∈ Ioo (-R) R) : J (-x) = -J x := by
  have hR : 0 < R := by norm_num
  have hy : x/R ∈ Ioo (-1:ℝ) 1 := ⟨(lt_div_iff₀ hR).mpr (by linarith [hx.1]), (div_lt_one hR).mpr hx.2⟩
  dsimp [J]; rw [neg_div, ← Real.tanh_artanh hy]
  simp only [← Real.tanh_neg, Real.artanh_tanh]

theorem integrated_obstruction (n : ℕ) (hn : 0 < n) (hβ : beta n < R)
    (θ : ℝ → ℝ) (s₁ s₂ : ℝ) (hs₁ : s₁ < w₀) (hs₂ : w₀ < s₂) (hgap : s₂-s₁ < beta n)
    (hθ : DifferentiableOn ℝ θ diameter)
    (hderiv : ∀ t ∈ Icc s₁ s₂, |deriv θ t| ≤ (2*logBound n/Real.pi)*R/(R^2-(t-w₀)^2))
    (hchange : |θ s₂-θ s₁| = Real.pi) :
    Real.pi ≤ (2*logBound n/Real.pi)*(J (w₀-s₁) + J (s₂-w₀)) ∧
    (2*logBound n/Real.pi)*(J (w₀-s₁) + J (s₂-w₀)) ≤ (2*logBound n/Real.pi)*J (beta n) ∧
    Real.pi^2 ≤ 2*logBound n*J (beta n) := by
  let C := 2*logBound n/Real.pi
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < logBound n := Real.log_pos (by linarith : (1:ℝ) < 90*n)
  have hC : 0 ≤ C := (div_pos (mul_pos (by norm_num) hlog) Real.pi_pos).le
  have hab := hs₁.trans hs₂
  have hmem {t : ℝ} (ht : t ∈ Icc s₁ s₂) : t ∈ diameter := by
    constructor <;> linarith [ht.1,ht.2]
  let P (t : ℝ) := C*J (t-w₀)
  have hP (t : ℝ) (ht : t ∈ Icc s₁ s₂) :
      HasDerivAt P (C*R/(R^2-(t-w₀)^2)) t := by
    have hm := hmem ht
    have hd := (artanh_primitive.2.1 _ (show t-w₀ ∈ Ioo (-R) R from
      ⟨by linarith [hm.1],by linarith [hm.2]⟩)).comp t ((hasDerivAt_id t).sub_const w₀)
    simpa [P,mul_div_assoc] using (hd.const_mul C)
  have hD (t : ℝ) (ht : t ∈ Icc s₁ s₂) :=
    (hθ.differentiableAt (isOpen_Ioo.mem_nhds (hmem ht))).hasDerivAt
  -- The two signs compare the phase increment with the same primitive.
  have compare (sign : ℝ) (hs : sign=1 ∨ sign= -1) :
      P s₁ + sign*θ s₁ ≤ P s₂ + sign*θ s₂ := by
    let F (t : ℝ) := P t+sign*θ t
    have hd (t) (ht : t ∈ Icc s₁ s₂) : HasDerivAt F
        (C*R/(R^2-(t-w₀)^2)+sign*deriv θ t) t := (hP t ht).add ((hD t ht).const_mul sign)
    have mono : MonotoneOn F (Icc s₁ s₂) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc ..)
        (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
        (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      intro t ht
      have ht' := interior_subset ht
      change 0 ≤ deriv F t
      rw [(hd t ht').deriv]
      obtain ⟨h₁,h₂⟩ := abs_le.mp (hderiv t ht')
      change -(C*R/_) ≤ _ at h₁
      change _ ≤ C*R/_ at h₂
      rcases hs with rfl | rfl <;> linarith
    exact mono (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab.le
  have hdiff : |θ s₂-θ s₁| ≤ P s₂-P s₁ := abs_le.mpr ⟨by linarith only [compare 1 (.inl rfl)],
    by linarith only [compare (-1) (.inr rfl)]⟩
  have hneg : J (s₁-w₀) = -J (w₀-s₁) := by
    rw [← neg_sub w₀ s₁]
    exact J_neg ⟨by linarith,by linarith⟩
  rw [hchange] at hdiff
  dsimp only [P] at hdiff
  rw [hneg] at hdiff
  have hfirst : Real.pi ≤ C*(J (w₀-s₁)+J (s₂-w₀)) := by linarith only [hdiff]
  have hsuper := artanh_primitive.2.2.2 (w₀-s₁) (s₂-w₀) (by linarith) (by linarith) (by linarith)
  rw [show w₀-s₁+(s₂-w₀)=s₂-s₁ by ring] at hsuper
  have hmono : J (s₂-s₁) ≤ J (beta n) := by
    apply Real.artanh_le_artanh
    · apply (lt_div_iff₀ (by norm_num : 0 < R)).mpr; linarith
    · exact (div_lt_one (by norm_num : 0 < R)).mpr hβ
    · exact div_le_div_of_nonneg_right hgap.le (by norm_num)
  have hsecond := mul_le_mul_of_nonneg_left (hsuper.trans hmono) hC
  refine ⟨hfirst,hsecond,?_⟩
  have h := hfirst.trans hsecond
  change Real.pi ≤ (2*logBound n/Real.pi)*J (beta n) at h
  rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos] at h
  linarith


private theorem ratio_at_eighty : 0.382099 < beta 80/R ∧ beta 80/R < 0.382100 := by
  have hs := Real.sq_sqrt (show 0 ≤ (160:ℝ) by norm_num)
  have hpos := Real.sqrt_pos.mpr (show 0 < (160:ℝ) by norm_num)
  have hlo : 12.6491106 < Real.sqrt 160 := (sq_lt_sq₀ (by norm_num) hpos.le).mp
    (by rw [hs]; norm_num)
  have hhi : Real.sqrt 160 < 12.6491107 := (sq_lt_sq₀ hpos.le (by norm_num)).mp
    (by rw [hs]; norm_num)
  norm_num [beta,R,div_div] at *
  constructor
  · apply (lt_div_iff₀ (by positivity)).mpr
    linarith only [hhi,Real.pi_gt_d6]
  · apply (div_lt_iff₀ (by positivity)).mpr
    linarith only [hlo,Real.pi_lt_d6]

private theorem log_at_eighty : 8.8818 < logBound 80 ∧ logBound 80 < 8.88185 := by
  have he : logBound 80 = 5*Real.log 2 + 2*Real.log 3 + 2*Real.log 5 := by
    rw [logBound, show 90*(80:ℝ) = 2^5 * 3^2 * 5^2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
    simp only [Real.log_pow]; norm_num
  rw [he]
  constructor
  · linarith only [Real.log_two_gt_d9,Real.log_three_gt_d9,Real.log_five_gt_d9]
  · linarith only [Real.log_two_lt_d9,Real.log_three_lt_d9,Real.log_five_lt_d9]

/-- Removing a log 2 leaves the Taylor series evaluated at a rational of
    modulus less than 0.12. Eight terms suffice for both enclosures. -/
private theorem log_artanh_bound (x : ℝ) (hx : x ∈ Ioo (-1:ℝ) 1)
    (u : ℝ) (hu : 1-u = ((1+x)/(1-x))/2) (hsmall : |u| < 1) :
    |(∑ i ∈ Finset.range 8, u^(i+1)/(i+1)) + 2*Real.artanh x - Real.log 2| ≤
      |u|^9/(1-|u|) := by
  have h := Real.abs_log_sub_add_sum_range_le hsmall 8
  rw [hu,Real.log_div (div_ne_zero (by linarith [hx.1]) (by linarith [hx.2])) (by norm_num)] at h
  rw [Real.artanh_eq_half_log ⟨hx.1.le,hx.2.le⟩]
  convert h using 2
  ring

private theorem J_at_eighty : 0.402515 < J (beta 80) ∧ J (beta 80) < 0.40252 := by
  obtain ⟨h₁,h₂⟩ := ratio_at_eighty
  have upper := log_artanh_bound 0.382100 (by constructor <;> norm_num)
    (1-((1+0.382100)/(1-0.382100))/2) (by norm_num) (by norm_num)
  have lower := log_artanh_bound 0.382099 (by constructor <;> norm_num)
    (1-((1+0.382099)/(1-0.382099))/2) (by norm_num) (by norm_num)
  have u := (abs_le.mp upper).2
  have l := (abs_le.mp lower).1
  norm_num [Finset.sum_range_succ] at u l
  have hm₁ := Real.artanh_lt_artanh (by norm_num : (-1:ℝ) < 0.382099) (by linarith : beta 80/R < 1) h₁
  have hm₂ := Real.artanh_lt_artanh (by linarith : (-1:ℝ) < beta 80/R) (by norm_num) h₂
  dsimp only [J]
  constructor
  · linarith only [l,hm₁,Real.log_two_gt_d9]
  · linarith only [u,hm₂,Real.log_two_lt_d9]

theorem threshold_components :
    0.382099 < beta 80/R ∧ beta 80/R < 0.382100 ∧
    8.8818 < logBound 80 ∧ logBound 80 < 8.88185 ∧
    0.402515 < J (beta 80) ∧ J (beta 80) < 0.40252 ∧
    2*logBound 80*J (beta 80) < 7.2 ∧ 9.8 < Real.pi^2 := by
  obtain ⟨hr₁,hr₂⟩ := ratio_at_eighty
  obtain ⟨hl₁,hl₂⟩ := log_at_eighty
  obtain ⟨hj₁,hj₂⟩ := J_at_eighty
  refine ⟨hr₁,hr₂,hl₁,hl₂,hj₁,hj₂,?_,?_⟩
  · calc
      2*logBound 80*J (beta 80) < 2*(8.88185:ℝ)*0.40252 :=
        mul_lt_mul_of_pos_of_nonneg' (mul_lt_mul_of_pos_left hl₂ (by norm_num)) hj₂.le
          ((by norm_num : (0:ℝ)<0.402515).trans hj₁) (by norm_num)
      _ < (7.2:ℝ) := by norm_num
  · nlinarith only [Real.pi_gt_d2, mul_self_lt_mul_self (by norm_num : (0:ℝ) ≤ 3.14) Real.pi_gt_d2]

theorem uniform_monotonicity :
    StrictMonoOn (fun u : ℝ => Real.artanh u/u) (Ioo 0 1) ∧
    StrictAntiOn (fun x : ℝ => logBound x/Real.sqrt x) (Ici 80) ∧
    (∀ x ∈ Ici (80:ℝ), J (beta x) ≤ Real.sqrt (80/x)*J (beta 80)) ∧
    StrictAntiOn (fun x : ℝ => 2*logBound x*J (beta x)) (Ici 80) := by
  have hconv : StrictConvexOn ℝ (Ico (0:ℝ) 1) Real.artanh := by
    simpa only [div_one] using scaled_convex (r := 1) zero_lt_one
  have hslope : StrictMonoOn (fun u : ℝ => Real.artanh u/u) (Ioo 0 1) := by
    intro x hx y hy hxy
    simpa only [Real.artanh_zero,sub_zero] using hconv.secant_strict_mono
      (show (0:ℝ) ∈ Ico 0 1 by simp) ⟨hx.1.le,hx.2⟩ ⟨hy.1.le,hy.2⟩ hx.1.ne' hy.1.ne' hxy
  have hlog (x : ℝ) (hx : x ∈ Ici (80:ℝ)) : 2 < logBound x := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<90*80) (mul_le_mul_of_nonneg_left hx (by norm_num : (0:ℝ)≤90))
    exact (by linarith only [log_at_eighty.1] : 2 < logBound 80) |>.trans_le h
  have hd (x : ℝ) (hx : x ∈ Ici (80:ℝ)) : HasDerivAt (fun u : ℝ => logBound u/Real.sqrt u)
      ((2-logBound x)/(2*x*Real.sqrt x)) x := by
    have hp : 0 < x := lt_of_lt_of_le (by norm_num : (0:ℝ)<80) hx
    have hs := Real.sqrt_pos.mpr hp
    have hl : HasDerivAt logBound (1/x) x := by
      apply ((((hasDerivAt_id x).const_mul (90:ℝ)).log (mul_pos (by norm_num) hp).ne')).congr_deriv
      dsimp; field_simp
    apply (hl.div (Real.hasDerivAt_sqrt hp.ne') hs.ne').congr_deriv
    generalize he : Real.sqrt x = y
    have hy : y^2 = x := he ▸ Real.sq_sqrt hp.le
    have hypos : 0 < y := he ▸ hs
    rw [← hy]; field_simp [hypos.ne']
  have hdec : StrictAntiOn (fun x : ℝ => logBound x/Real.sqrt x) (Ici 80) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici _) (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    intro x hx
    have h := interior_subset hx
    rw [(hd x h).deriv]
    exact div_neg_of_neg_of_pos (sub_neg.mpr (hlog x h)) (by have : 0 < x := lt_of_lt_of_le (by norm_num : (0:ℝ)<80) h; positivity)
  let c := Real.pi/(Real.sqrt 2*R)
  have hc : 0 < c := by dsimp [c,R]; positivity
  have hβ (x : ℝ) : beta x/R = c/Real.sqrt x := by
    dsimp [beta,c]; rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]; ring
  have hu (x : ℝ) (hx : x ∈ Ici (80:ℝ)) : c/Real.sqrt x ∈ Ioo (0:ℝ) 1 := by
    have hp : 0 < x := lt_of_lt_of_le (by norm_num : (0:ℝ)<80) hx
    refine ⟨div_pos hc (Real.sqrt_pos.mpr hp), ?_⟩
    have h := div_le_div_of_nonneg_left hc.le (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<80)) (Real.sqrt_le_sqrt hx)
    rw [← hβ 80] at h
    exact h.trans_lt (by linarith only [ratio_at_eighty.2])
  let Q (x : ℝ) := Real.artanh (c/Real.sqrt x)/(c/Real.sqrt x)
  have hQ (x : ℝ) (hx : x ∈ Ici (80:ℝ)) : 0 < Q x :=
    div_pos (Real.artanh_pos (hu x hx)) (hu x hx).1
  have hanti : StrictAntiOn Q (Ici 80) := by
    intro x hx y hy hxy
    exact hslope (hu y hy) (hu x hx) (div_lt_div_of_pos_left hc
      (Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num : (0:ℝ)<80) hx)) (Real.sqrt_lt_sqrt (by linarith [show (80:ℝ) ≤ x from hx]) hxy))
  have hid (x : ℝ) (hx : x ∈ Ici (80:ℝ)) : J (beta x) = (c/Real.sqrt x)*Q x := by
    dsimp only [J,Q]; rw [hβ, mul_div_cancel₀ _ (hu x hx).1.ne']
  refine ⟨hslope,hdec,?_,?_⟩
  · intro x hx
    have hp : 0 < x := lt_of_lt_of_le (by norm_num : (0:ℝ)<80) hx
    rw [hid _ hx,hid 80 (mem_Ici.mpr le_rfl),Real.sqrt_div (by norm_num : (0:ℝ) ≤ 80)]
    calc
      _ ≤ c/Real.sqrt x*Q 80 := mul_le_mul_of_nonneg_left (hanti.antitoneOn (mem_Ici.mpr le_rfl) hx hx) (hu _ hx).1.le
      _ = _ := by field_simp
  · intro x hx y hy hxy
    change 2*logBound y*J (beta y) < 2*logBound x*J (beta x)
    rw [hid x hx,hid y hy, show 2*logBound y*(c/Real.sqrt y*Q y) =
      (2*c)*(logBound y/Real.sqrt y*Q y) by ring,
      show 2*logBound x*(c/Real.sqrt x*Q x) = (2*c)*(logBound x/Real.sqrt x*Q x) by ring]
    apply mul_lt_mul_of_pos_left _ (by positivity)
    exact mul_lt_mul_of_pos_of_nonneg' (hdec hx hy hxy) (hanti hx hy hxy).le
      (hQ _ hy) (div_nonneg ((by norm_num : (0:ℝ)≤2).trans (hlog x hx).le) (Real.sqrt_nonneg _))

end Turan.TrinomialAE
