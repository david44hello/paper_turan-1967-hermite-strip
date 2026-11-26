module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Degree
public import Turan.Rouche
public import Turan.Sturm
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

noncomputable section
open Polynomial Metric Set
open scoped ComplexConjugate
namespace Turan.TrinomialLarge

private abbrev center : ℂ := (-1/2 : ℝ)
private abbrev radius : ℝ := 65/100
private abbrev outer : ℝ := 76/100
private def pencil (n : ℕ) (a : ℂ) : Polynomial ℂ := 1 + 2 * X + C a * hermite n

private theorem pencil_eval (n : ℕ) (a z : ℂ) :
    (pencil n a).eval z = 1 + 2*z + a*(hermite n).eval z := by
  simp [pencil, eval_add, eval_mul]

private theorem pencil_reflect (n : ℕ) (a z : ℂ) :
    (pencil n (conj a)).eval z = conj ((pencil n a).eval (conj z)) := by
  simp [pencil_eval, (hermite_symmetry n z).1, map_ofNat]

private theorem pencil_degree (n : ℕ) (hn : 1 ≤ n) (a : ℂ) : (pencil n a).natDegree ≤ n := by
  apply (natDegree_add_le ..).trans (max_le ?_ ((natDegree_C_mul_le ..).trans (hermite_degree n).1.le))
  apply (natDegree_add_le ..).trans (max_le (by simp) ?_)
  simpa using hn

/-- Differentiate the product of the linear factors once and twice. Each
    removed factor costs at most D, since its modulus is at least 1/D. -/
private theorem product_derivatives (a z : ℂ) (D : ℝ) (hD : 0 ≤ D)
    (s : Multiset ℂ) (p : Polynomial ℂ) (hp : p = C a * (s.map (X - C ·)).prod)
    (hsep : ∀ w ∈ s, 1 ≤ D * ‖z-w‖) :
    ‖p.derivative.eval z‖ ≤ s.card * D * ‖p.eval z‖ ∧
    ‖p.derivative.derivative.eval z‖ ≤ (s.card * D)^2 * ‖p.eval z‖ := by
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
          nlinarith only [h₁', mul_le_mul_of_nonneg_left h₂ (norm_nonneg (z-w)),
              mul_nonneg (sq_nonneg D) (mul_nonneg (norm_nonneg (z-w)) (norm_nonneg (q.eval z)))]

private theorem operator_identity (n : ℕ) (a z : ℂ) :
    let p := pencil n a
    (n : ℂ)*p.eval z + p.derivative.derivative.eval z/2 - z*p.derivative.eval z =
      ((n : ℂ)-1)*(1+2*z)+1 := by
  have he := congrArg (fun P : Polynomial ℂ => P.eval z) (hermite_equation n)
  simp only [eval_sub, eval_neg, eval_natCast, eval_mul, eval_X, eval_ofNat, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_ofNat] at he
  dsimp only
  simp [pencil, derivative_add, derivative_mul, eval_add, eval_mul]
  linear_combination (a/2)*he

private theorem reflect_dist (z : ℂ) : dist (conj z) center = dist z center := by
  simpa only [Complex.conj_ofReal] using (Complex.isometry_conj.dist_eq z center)

private theorem linear_bound (n : ℕ) (hn : 80 ≤ n) (a : ℂ)
    (hfree : ∀ v ∈ ball center outer, (pencil n a).eval v ≠ 0)
    {z : ℂ} (hz : z ∈ sphere center radius) :
    ‖1 + 2*z‖ ≤ 55 * n * ‖(pencil n a).eval z‖ := by
  let p := pencil n a
  have hn' : (80 : ℝ) ≤ n := by exact_mod_cast hn
  have hsep (w : ℂ) (hw : w ∈ p.roots) : 1 ≤ 10 * ‖z-w‖ := by
    have hout : outer ≤ dist w center := by
      by_contra! hin
      exact hfree w hin (isRoot_of_mem_roots hw)
    have htri := dist_triangle w z center
    rw [dist_comm w z, dist_eq_norm z w, mem_sphere.mp hz] at htri
    dsimp [outer, radius] at *
    linarith
  obtain ⟨hd₁, hd₂⟩ := product_derivatives p.leadingCoeff z 10 (by norm_num) p.roots p
    (IsAlgClosed.splits p).eq_prod_roots hsep
  have hcard : (p.roots.card : ℝ) ≤ n := by
    exact_mod_cast (p.card_roots').trans (pencil_degree n (by omega) a)
  have h₁ : ‖p.derivative.eval z‖ ≤ (n:ℝ)*10*‖p.eval z‖ := by grw [hd₁, hcard]
  have h₂ : ‖p.derivative.derivative.eval z‖ ≤ ((n:ℝ)*10)^2 * ‖p.eval z‖ := by grw [hd₂, hcard]
  have hc : ‖center‖ = 1/2 := by norm_num [center]
  have hz' : ‖z‖ ≤ 115/100 := by
    have h' := norm_add_le (z-center) center
    rw [sub_add_cancel, ← dist_eq_norm, mem_sphere.mp hz, hc] at h'
    norm_num [radius] at h' ⊢
    exact h'
  let L := 1 + 2*z
  have hL : ‖L‖ = 13/10 := by
    have h : L = 2*(z-center) := by dsimp [L, center]; push_cast; ring
    rw [h, norm_mul, ← dist_eq_norm, mem_sphere.mp hz]
    norm_num [radius]
  let T := ((n:ℂ)-1)*L + 1
  have hlower : ((n:ℝ)-1)*(13/10) ≤ ‖T‖ + 1 := by
    have h := norm_sub_le T 1
    have hnorm : ‖(n:ℂ)-1‖ = (n:ℝ)-1 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    simpa only [T, add_sub_cancel_right, norm_mul, hnorm, hL, norm_one] using h
  have hupper : ‖T‖ ≤ (51*(n:ℝ)^2)*‖p.eval z‖ := by
    rw [show T = (n : ℂ)*p.eval z + p.derivative.derivative.eval z/2 -
        z*p.derivative.eval z from (operator_identity n a z).symm]
    calc
      _ ≤ (n:ℝ)*‖p.eval z‖ + ‖p.derivative.derivative.eval z‖/2 + ‖z‖*‖p.derivative.eval z‖ := by
        grw [norm_sub_le, norm_add_le]; simp
      _ ≤ (n:ℝ)*‖p.eval z‖ + (((n:ℝ)*10)^2 * ‖p.eval z‖)/2 +
          (115/100)*((n:ℝ)*10*‖p.eval z‖) := by gcongr
      _ ≤ _ := by
        have h := mul_nonneg (show 0 ≤ (n:ℝ)*((n:ℝ)-25/2) by exact mul_nonneg (by positivity) (by linarith)) (norm_nonneg (p.eval z))
        nlinarith only [h]
  change ‖L‖ ≤ _
  rw [hL]
  by_contra! hbad
  nlinarith only [hlower, hupper, hn', mul_lt_mul_of_pos_left hbad (show 0 < (n:ℝ) by linarith)]

/-- The polynomial argument principle gives the maximum modulus bound for a
    rational function Q/P. If λ is a larger value inside the circle, then
    λP − Q would have a zero there, contradicting its Rouché count. -/
private theorem polynomial_ratio_max (P Q : Polynomial ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hP : ∀ z ∈ closedBall center radius, P.eval z ≠ 0)
    (hbd : ∀ z ∈ sphere center radius, ‖Q.eval z / P.eval z‖ ≤ B)
    {v : ℂ} (hv : v ∈ ball center radius) : ‖Q.eval v / P.eval v‖ ≤ B := by
  by_contra! hlarge
  let c := Q.eval v / P.eval v
  have hc : c ≠ 0 := norm_pos_iff.mp (hB.trans_lt hlarge)
  let S := C c * P
  let T := S - Q
  have hdom (w : ℂ) (hw : w ∈ sphere center radius) : ‖T.eval w - S.eval w‖ < ‖S.eval w‖ := by
    have h := (hbd w hw).trans_lt hlarge
    rw [norm_div, div_lt_iff₀ (norm_pos_iff.mpr (hP w (sphere_subset_closedBall hw)))] at h
    simpa [T, S, eval_sub, eval_mul, norm_mul, c] using h
  have hT : T ≠ 0 := by
    intro h
    have := hdom _ (circleMap_mem_sphere center (by norm_num : 0 ≤ radius) 0)
    simp [h] at this
  have hvT : v ∈ T.roots := (mem_roots hT).mpr (by
    change T.eval v = 0
    simp [T, S, c, eval_sub, eval_mul, hP v (ball_subset_closedBall hv)])
  have hpositive := Multiset.card_pos_iff_exists_mem.mpr
    ⟨v, Multiset.mem_filter_of_mem (p := fun z => dist z center < radius) hvT hv⟩
  rw [polynomial_rouche S T center radius (by norm_num) hdom] at hpositive
  obtain ⟨w, hw⟩ := Multiset.card_pos_iff_exists_mem.mp hpositive
  obtain ⟨hwS, hwin⟩ := Multiset.mem_filter.mp hw
  have hnz := mul_ne_zero hc (hP w (ball_subset_closedBall hwin))
  exact hnz (by simpa [S, IsRoot.def, eval_mul] using isRoot_of_mem_roots hwS)

private theorem ratio_bound (n : ℕ) (hn : 80 ≤ n) (a : ℂ)
    (hfree : ∀ v ∈ ball center outer, (pencil n a).eval v ≠ 0)
    {z : ℂ} (hz : z ∈ ball center radius) :
    ‖(pencil n (conj a)).eval z / (pencil n a).eval z‖ ≤ 120*n := by
  have hrad : radius < outer := by norm_num [radius, outer]
  have hcl (v : ℂ) (hv : v ∈ closedBall center radius) :=
    hfree v (closedBall_subset_ball hrad hv)
  apply polynomial_ratio_max _ _ _ (by positivity) hcl (fun v hs => ?_) hz
  have hnon := hcl v (sphere_subset_closedBall hs)
  have ha : a ≠ 0 := by
    intro h
    have := hfree center (mem_ball_self (by norm_num : 0 < outer))
    norm_num [pencil_eval, h, center] at this
  let u := conj a / a
  have hu : ‖u‖ = 1 := by simp [u, ha]
  have hu' : ‖1-u‖ ≤ 2 := by have := norm_sub_le (1:ℂ) u; rw [norm_one, hu] at this; linarith
  have hid : (pencil n (conj a)).eval v =
      u*(pencil n a).eval v + (1-u)*(1+2*v) := by
    simp only [pencil_eval, u]; field_simp; ring
  change ‖(pencil n (conj a)).eval v / (pencil n a).eval v‖ ≤ _
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hnon), hid]
  calc
    _ ≤ ‖u‖*‖(pencil n a).eval v‖ + ‖1-u‖*‖1+2*v‖ := by
      simpa only [norm_mul] using norm_add_le (u*(pencil n a).eval v) ((1-u)*(1+2*v))
    _ ≤ 1*‖(pencil n a).eval v‖ + 2*(55*n*‖(pencil n a).eval v‖) := by
      rw [hu]; gcongr; exact linear_bound n hn a hfree hs
    _ ≤ _ := by
      have hn' : (80:ℝ) ≤ n := by exact_mod_cast hn
      nlinarith only [mul_nonneg (show 0 ≤ 10*(n:ℝ)-1 by linarith) (norm_nonneg ((pencil n a).eval v))]

/-- Prescribe the value of a primitive of p'/p at the center. Differentiating
    p exp(-L) shows that this primitive is a logarithm of p throughout the disk. -/
private theorem disk_log (p : Polynomial ℂ) (hfree : ∀ v ∈ ball center radius, p.eval v ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball center radius) ∧
      ∀ v ∈ ball center radius, Complex.exp (L v) = p.eval v := by
  have hc : center ∈ ball center radius := mem_ball_self (by norm_num)
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

/-- A largest zero on the left followed by one Sturm comparison gives two
    zeros on opposite sides of the center at distance less than π/k. -/
private theorem bracketing_zeros (n : ℕ) (k : ℝ) (hk : 0 < k) (hk₂ : k^2 = 2*(n:ℝ))
    (hβ : Real.pi/k < 1/4) (hc : psi n center ≠ 0) :
    ∃ s t : ℝ, s < -1/2 ∧ -1/2 < t ∧ t-s < Real.pi/k ∧ psi n s = 0 ∧ psi n t = 0 := by
  let c : ℝ := -1/2
  let β := Real.pi/k
  have hb : 0 < β := div_pos Real.pi_pos hk
  have hit (u : ℝ) (hu : c-β ≤ u) (hu' : u ≤ c) :
      ∃ v ∈ Ioo u (u+β), psi n v = 0 := by
    apply hermite_sturm_interval n u k hk
    intro v hv
    have h₁ : -1 < v := by dsimp [c, β] at *; linarith [hv.1]
    have h₂ : v < 1 := by dsimp [c, β] at *; linarith [hv.2]
    nlinarith only [hk₂, mul_pos (by linarith : 0 < v+1) (by linarith : 0 < 1-v)]
  let S := Icc (c-β) c ∩ {v : ℝ | psi n (v:ℂ) = 0}
  have hcont : Continuous (fun v : ℝ => psi n v) :=
    ((hermite n).continuous.div_const _).comp Complex.continuous_ofReal
  have hcompact : IsCompact S := isCompact_Icc.inter_right (isClosed_eq hcont continuous_const)
  obtain ⟨u, hu, hpu⟩ := hit (c-β) le_rfl (by linarith)
  have hS : S.Nonempty := ⟨u, ⟨hu.1.le, by linarith [hu.2]⟩, hpu⟩
  obtain ⟨s, hs, hmax⟩ := hcompact.exists_isMaxOn hS (continuous_id.continuousOn)
  obtain ⟨t, ht, hpt⟩ := hit s hs.1.1 hs.1.2
  have hsc : s < c := by
    apply lt_of_le_of_ne hs.1.2
    intro he
    have hps : psi n (s:ℂ) = 0 := hs.2
    rw [he] at hps
    exact hc hps
  have hct : c < t := by
    by_contra! h
    have htS : t ∈ S := ⟨⟨hs.1.1.trans ht.1.le, h⟩, hpt⟩
    exact ht.1.not_ge (hmax htS)
  exact ⟨s, t, hsc, hct, by linarith [ht.2], hs.2, hpt⟩

/-- Invert the real Cayley transform on the part of the disk used by the
    Sturm endpoints. This elementary bound replaces integration of artanh. -/
private theorem cayley_real (y d : ℝ) (hd : 0 ≤ d) (hd' : d ≤ 2/5)
    (h : |Real.exp y - 1| ≤ d * (Real.exp y + 1)) : |y| ≤ (8/3)*d := by
  have h₁ : 0 < 1-d := by linarith
  have h₂ : 0 < 1+d := by linarith
  have upper (x : ℝ) (hx : Real.exp x * (1-d) ≤ 1+d) : x ≤ (8/3)*d := by
    have hlog := Real.log_le_log (Real.exp_pos x) ((le_div_iff₀ h₁).mpr hx)
    rw [Real.log_exp, Real.log_div h₂.ne' h₁.ne'] at hlog
    have hneg := Real.log_le_sub_one_of_pos (inv_pos.mpr h₁)
    rw [Real.log_inv] at hneg
    have hrec : (1-d)⁻¹-1 ≤ (5/3)*d := by
      rw [sub_le_iff_le_add, inv_le_iff_one_le_mul₀ h₁]
      nlinarith only [mul_nonneg hd (show 0 ≤ 2/5-d by linarith)]
    linarith [Real.log_le_sub_one_of_pos h₂]
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  apply abs_le.mpr
  constructor
  · have hn := upper (-y) (by
      rw [Real.exp_neg, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos y)]
      linarith)
    linarith
  · apply upper
    linarith

/-- A holomorphic map U into the horizontal strip, vanishing at the center,
    obeys an explicit Schwarz bound at any point where its value is real. -/
private theorem schwarz_strip_real (U : ℂ → ℂ) (hU : DifferentiableOn ℂ U (ball center radius))
    (hzero : U center = 0) (hstrip : ∀ z ∈ ball center radius, |(U z).im| < Real.pi/2)
    (s : ℂ) (hs : dist s center < 1/4) (y : ℝ) (hy : U s = (y:ℂ)) :
    |y| ≤ (8/3) * (dist s center / radius) := by
  let E (z : ℂ) := Complex.exp (U z)
  let A (z : ℂ) := (E z - 1)/(E z + 1)
  have hpos (z : ℂ) (hz : z ∈ ball center radius) : 0 < (E z).re :=
    by rw [show (E z).re = _ from Complex.exp_re _]
       exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp (hstrip z hz)))
  have hden (z : ℂ) (hz : z ∈ ball center radius) : E z + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    linarith [hpos z hz]
  have hA : DifferentiableOn ℂ A (ball center radius) :=
    (hU.cexp.sub_const 1).div (hU.cexp.add_const 1) hden
  have hA₀ : A center = 0 := by
    change (Complex.exp (U center)-1)/(Complex.exp (U center)+1) = 0
    rw [hzero]; norm_num
  have hmaps : MapsTo A (ball center radius) (closedBall (A center) 1) := by
    intro z hz
    rw [hA₀, mem_closedBall, dist_zero_right]
    change ‖(E z - 1)/(E z + 1)‖ ≤ 1
    rw [norm_div, div_le_one (norm_pos_iff.mpr (hden z hz))]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, add_zero, sub_zero]
    nlinarith only [hpos z hz]
  have hsmall : s ∈ ball center radius := lt_trans hs (by norm_num)
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball hA hmaps hsmall
  rw [hA₀, dist_zero_right] at h
  have hvalue : A s = (((Real.exp y - 1)/(Real.exp y + 1) : ℝ):ℂ) := by
    simp [A, E, hy, Complex.ofReal_exp]
  rw [hvalue, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : 0 < Real.exp y + 1),
    div_le_iff₀ (by positivity : 0 < Real.exp y + 1)] at h
  apply cayley_real _ _ (by positivity) ((div_le_iff₀ (by norm_num : 0 < radius)).mpr (by
    dsimp [radius]; linarith))
  convert h using 1
  ring

private theorem phase_scale (k : ℝ) (hk : 25/2 ≤ k) :
    60*k^2 < Real.exp (3/4*k) := by
  have hbase : (100 : ℝ) < Real.exp (75/16) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (75/16 : ℝ)) 10
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hpow : 8*k ≤ Real.exp (3/8*k) := by
    rw [show 3/8*k = 75/16 + (3/8*k-75/16) by ring, Real.exp_add]
    calc
      _ ≤ 100*((3/8*k-75/16)+1) := by linarith
      _ ≤ _ := mul_le_mul hbase.le (Real.add_one_le_exp _) (by linarith) (Real.exp_pos _).le
  rw [show 3/4*k = 3/8*k + 3/8*k by ring, Real.exp_add]
  nlinarith only [mul_self_le_mul_self (show 0 ≤ 8*k by linarith) hpow,
    sq_pos_of_pos (by linarith : 0 < k)]

/-- Apply the strip estimate to the antisymmetric part of the logarithm.
    On the real diameter it measures exactly twice the change in phase. -/
private theorem phase_at_real (n : ℕ) (hn : 80 ≤ n) (a : ℂ)
    (hfree : ∀ v ∈ ball center outer, (pencil n a).eval v ≠ 0)
    (k : ℝ) (hk : 25/2 ≤ k) (hk₂ : k^2 = 2*(n:ℝ))
    (L : ℂ → ℂ) (hL : DifferentiableOn ℂ L (ball center radius))
    (hexp : ∀ v ∈ ball center radius, Complex.exp (L v) = (pencil n a).eval v)
    (s : ℝ) (hs : dist (s:ℂ) center < 1/4) :
    2*(52/25/k)*|(L s).im - (L center).im| ≤ (8/3)*(dist (s:ℂ) center/radius) := by
  let κ := 52/25/k
  have hkpos : 0 < k := by linarith
  have hκ : 0 < κ := div_pos (by norm_num) hkpos
  have hscale : κ*(3/4*k) = 39/25 := by dsimp [κ]; field_simp; ring
  let F (z : ℂ) := L z - conj (L (conj z))
  let U (z : ℂ) := (κ:ℂ) * Complex.I * (F z-F center)
  have hconj (z : ℂ) (hz : z ∈ ball center radius) : conj z ∈ ball center radius := by
    rwa [mem_ball, reflect_dist]
  have hre (z : ℂ) (hz : z ∈ ball center radius) :
      (L (conj z)).re - (L z).re < 3/4*k := by
    apply Real.exp_lt_exp.mp
    calc
      _ = ‖(pencil n (conj a)).eval z / (pencil n a).eval z‖ := by
        rw [Real.exp_sub, ← Complex.norm_exp, ← Complex.norm_exp, hexp _ (hconj _ hz),
          hexp _ hz, pencil_reflect, norm_div, Complex.norm_conj]
      _ ≤ _ := ratio_bound n hn a hfree hz
      _ < _ := by rw [show 120*(n:ℝ) = 60*k^2 by linarith]; exact phase_scale k hk
  have hF : DifferentiableOn ℂ F (ball center radius) := by
    apply hL.sub
    intro z hz
    have hd := (hL.differentiableAt (isOpen_ball.mem_nhds (hconj z hz))).conj_conj
    simpa only [Complex.conj_conj, Function.comp_def] using hd.differentiableWithinAt
  have hU : DifferentiableOn ℂ U (ball center radius) := (hF.sub_const _).const_mul _
  have hstrip (z : ℂ) (hz : z ∈ ball center radius) : |(U z).im| < Real.pi/2 := by
    have hh := hre (conj z) (hconj z hz)
    rw [Complex.conj_conj] at hh
    have hlo := mul_lt_mul_of_pos_left (hre z hz) hκ
    have hhi := mul_lt_mul_of_pos_left hh hκ
    rw [hscale] at hlo hhi
    have him : (U z).im = κ*((L z).re-(L (conj z)).re) := by
      simp [U, F, Complex.mul_im, Complex.mul_re, center, map_ofNat]
    rw [him]
    apply abs_lt.mpr
    constructor <;> nlinarith only [hlo, hhi, Real.pi_gt_d2]
  have hy : U s = ((-(2*κ*((L s).im-(L center).im)) : ℝ):ℂ) := by
    apply Complex.ext <;> simp [U, F, center, Complex.mul_im, Complex.mul_re, map_ofNat]
    ring
  have h := schwarz_strip_real U hU (by simp [U]) hstrip s hs _ hy
  simpa only [abs_neg, abs_mul, abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) hκ)] using h

private theorem phase_jump {u v : ℂ} {b : ℝ} (hb : b < 0)
    (h : Complex.exp (u-v) = (b:ℂ)) : Real.pi ≤ |u.im-v.im| := by
  by_contra! hsmall
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hsmall
  have ha := congrArg Complex.arg h
  rw [Complex.arg_exp, Complex.sub_im, Complex.arg_ofReal_of_neg hb,
    (toIocMod_eq_self Real.two_pi_pos).mpr ⟨hlo, by linarith⟩] at ha
  linarith

private theorem disk_zero (n : ℕ) (hn : 80 ≤ n) (a : ℂ) :
    ∃ z ∈ ball center outer, (pencil n a).eval z = 0 := by
  by_contra! hfree
  let k := Real.sqrt (2*(n:ℝ))
  have hn' : (80:ℝ) ≤ n := by exact_mod_cast hn
  have hkpos : 0 < k := Real.sqrt_pos.mpr (by positivity)
  have hk₂ : k^2 = 2*(n:ℝ) := Real.sq_sqrt (by positivity)
  have hk : 63/5 ≤ k := by
    apply (sq_le_sq₀ (by norm_num) hkpos.le).mp
    nlinarith only [hk₂, hn']
  have hb : Real.pi/k < 1/4 := (div_lt_iff₀ hkpos).mpr (by linarith [Real.pi_lt_d2])
  have hden : (Real.sqrt (2^n * (n.factorial:ℝ)) : ℂ) ≠ 0 := by
    have := Nat.factorial_pos n
    exact_mod_cast (show (0:ℝ) < Real.sqrt (2^n * (n.factorial:ℝ)) by positivity).ne'
  have hroot (v : ℂ) (hv : psi n v = 0) : (hermite n).eval v = 0 :=
    (div_eq_zero_iff.mp hv).resolve_right hden
  have hc : psi n center ≠ 0 := by
    intro h
    have hbad := hfree center (mem_ball_self (by norm_num : 0 < outer))
    apply hbad
    rw [pencil_eval, hroot center h]
    norm_num [center]
  obtain ⟨s, t, hs, ht, hgap, hps, hpt⟩ := bracketing_zeros n k hkpos hk₂ hb hc
  have hdist (v : ℝ) : dist (v:ℂ) center = |v-(-1/2)| := by
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have ds : dist (s:ℂ) center = -1/2-s := by rw [hdist, abs_of_neg (by linarith)]; ring
  have dt : dist (t:ℂ) center = t-(-1/2) := by rw [hdist, abs_of_pos (by linarith)]
  have hs' : dist (s:ℂ) center < 1/4 := by rw [ds]; linarith
  have ht' : dist (t:ℂ) center < 1/4 := by rw [dt]; linarith
  obtain ⟨L, hL, he⟩ := disk_log (pencil n a) (fun v hv => hfree v (ball_subset_ball
    (by norm_num : radius ≤ outer) hv))
  have hphase := phase_at_real n hn a hfree k (by linarith) hk₂ L hL he
  have h₁ := hphase s hs'
  have h₂ := hphase t ht'
  rw [ds] at h₁
  rw [dt] at h₂
  have hnegative : Complex.exp (L s - L t) = (((1+2*s)/(1+2*t) : ℝ):ℂ) := by
    rw [Complex.exp_sub, he s (lt_trans hs' (by norm_num : 1/4 < radius)),
      he t (lt_trans ht' (by norm_num : 1/4 < radius)), pencil_eval, pencil_eval,
      hroot s hps, hroot t hpt]
    push_cast
    ring
  have hjump := phase_jump (div_neg_of_neg_of_pos (by linarith : 1+2*s<0)
    (by linarith : 0<1+2*t)) hnegative
  have hsum := abs_sub_le (L s).im (L center).im (L t).im
  rw [abs_sub_comm (L center).im] at hsum
  have hκ : 0 < 2*(52/25/k) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left (hjump.trans hsum) hκ.le
  rw [mul_add] at hscaled
  dsimp [radius] at h₁ h₂
  have hnum : 2*(52/25/k)*Real.pi ≤ (8/3)*(t-s)/(65/100) := by
    linarith only [hscaled, h₁, h₂]
  have hshort := (lt_div_iff₀ hkpos).mp hgap
  field_simp [hkpos.ne'] at hnum
  nlinarith only [hnum, hshort, Real.pi_pos]

end Turan.TrinomialLarge

namespace Turan
open TrinomialLarge

/-- For n ≥ 80 the zero supplied by the disk argument lies strictly inside
    the requested rectangle. -/
theorem trinomial_large (n : ℕ) (hn : 80 ≤ n) (a : ℂ) :
    ∃ c : ℂ, 1 + 2*c + a*psi n c = 0 ∧ |c.re| ≤ 2 ∧ |c.im| < 76/100 := by
  let d : ℂ := Real.sqrt (2^n * (n.factorial:ℝ))
  obtain ⟨c, hc, hroot⟩ := disk_zero n hn (a/d)
  rw [pencil_eval] at hroot
  refine ⟨c, ?_, ?_, ?_⟩
  · change 1+2*c+a*((hermite n).eval c/d) = 0
    linear_combination hroot
  · have hx := (Complex.abs_re_le_norm (c-TrinomialLarge.center)).trans_lt (show ‖c-TrinomialLarge.center‖ < outer by
      rwa [← dist_eq_norm])
    rw [Complex.sub_re, Complex.ofReal_re, abs_lt] at hx
    apply abs_le.mpr
    constructor <;> dsimp [outer] at hx <;> linarith [hx.1, hx.2]
  · have hy := (Complex.abs_im_le_norm (c-TrinomialLarge.center)).trans_lt (show ‖c-TrinomialLarge.center‖ < outer by
      rwa [← dist_eq_norm])
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hy

end Turan
