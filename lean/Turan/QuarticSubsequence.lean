module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.CompactnessTools
public import Turan.QuarticEscape
public import Turan.QuarticStability
public import Turan.QuarticCandidate
public import Turan.QuarticRoot
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

@[expose] public section

noncomputable section
open Filter Polynomial Metric
open scoped Topology
namespace Turan

/-- The finite (2,4) family always has a lowest zero (family_has_lowest_zero). -/
def quarticFamilyHeight (p : ℂ × ℂ) : ℝ :=
  sInf {r : ℝ | ∃ z : ℂ, (family 2 4 p.1 p.2).eval z = 0 ∧ |z.im| = r}


private theorem nonzero_coords_of_unit {q : ℂ × ℂ} (hq : ‖q‖ = 1) :
    q.1 ≠ 0 ∨ q.2 ≠ 0 := by
  by_contra! h
  have he : q = 0 := Prod.ext h.1 h.2
  simp [he] at hq

private theorem homogeneous_ne_zero {a b : ℂ} (hab : a ≠ 0 ∨ b ≠ 0) :
    C a * hermite 2 + C b * hermite 4 ≠ 0 := by
  intro h
  have he (z : ℂ) := congrArg (eval z) h
  have h₀ := he 0
  have h₁ := he 1
  norm_num [hermite, eval_add, eval_mul, eval_sub, nsmul_eq_mul] at h₀ h₁
  rcases hab with ha | hb
  · apply ha
    linear_combination (-5/4 : ℂ) * h₀ - (3/4 : ℂ) * h₁
  · apply hb
    linear_combination (-1/8 : ℂ) * h₀ - (1/8 : ℂ) * h₁

private def scaledEval (v : ℝ × (ℂ × ℂ)) : C(ℂ, ℂ) :=
  ⟨fun z => (v.1 : ℂ) * (1 + 2*z) + v.2.1*(hermite 2).eval z + v.2.2*(hermite 4).eval z,
   by fun_prop⟩

private theorem continuous_scaledEval : Continuous scaledEval := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  dsimp [Function.uncurry, scaledEval]
  fun_prop

/-- The product norm on the coefficient pair is M = max (‖a‖) (‖b‖). -/
theorem quartic_unbounded_normalized_subsequence (p : ℕ → ℂ × ℂ)
    (hunbounded : ¬ BddAbove (Set.range (fun j => ‖p j‖))) :
    ∃ (σ : ℕ → ℕ) (q : ℂ × ℂ), StrictMono σ ∧
      Tendsto (fun k => ‖p (σ k)‖) atTop atTop ∧ ‖q‖ = 1 ∧
      Tendsto (fun k => (‖p (σ k)‖)⁻¹ • p (σ k)) atTop (𝓝 q) ∧
      let G := C q.1 * hermite 2 + C q.2 * hermite 4
      G ≠ 0 ∧ TendstoLocallyUniformly
        (fun k z => (family 2 4 (p (σ k)).1 (p (σ k)).2).eval z / (‖p (σ k)‖ : ℂ))
        (fun z => G.eval z) atTop := by
  have hfreq (R : ℝ) : ∃ᶠ i in atTop, R < ‖p i‖ := by
    by_contra! h
    exact hunbounded (Filter.IsBoundedUnder.bddAbove_range ⟨R,h⟩)
  obtain ⟨τ,hτ,hM⟩ := Filter.subseq_tendsto_of_neBot (u := fun i => ‖p i‖)
    (f := atTop) (Filter.inf_map_atTop_neBot_iff.mpr (by
      intro U hU N
      obtain ⟨R,hR⟩ := Filter.mem_atTop_sets.mp hU
      obtain ⟨i,hi,hgt⟩ := Filter.frequently_atTop.mp (hfreq R) N
      exact ⟨i,hi,hR _ hgt.le⟩))
  let d := fun i => ‖p (τ i)‖⁻¹ • p (τ i)
  have hd : ∀ᶠ i in atTop, d i ∈ sphere (0 : ℂ × ℂ) 1 := by
    filter_upwards [hM.eventually (eventually_gt_atTop 0)] with i hi
    change 0 < ‖p (τ i)‖ at hi
    rw [mem_sphere_zero_iff_norm]
    change ‖‖p (τ i)‖⁻¹ • p (τ i)‖ = 1
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hi), inv_mul_cancel₀ hi.ne']
  obtain ⟨q,hq,φ,hφ,hconv⟩ := (isCompact_sphere (0 : ℂ × ℂ) 1).tendsto_subseq' hd.frequently
  let σ := τ ∘ φ
  have hnorm : ‖q‖ = 1 := mem_sphere_zero_iff_norm.mp hq
  have hdiv : Tendsto (fun k => ‖p (σ k)‖) atTop atTop := hM.comp hφ.tendsto_atTop
  have hdir : Tendsto (fun k => ‖p (σ k)‖⁻¹ • p (σ k)) atTop (𝓝 q) := hconv
  refine ⟨σ,q,hτ.comp hφ,hdiv,hnorm,hdir,homogeneous_ne_zero (nonzero_coords_of_unit hnorm),?_⟩
  have ht := (tendsto_inv_atTop_zero.comp hdiv).prodMk_nhds hdir
  have hlocal := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp
    (continuous_scaledEval.continuousAt.tendsto.comp ht)
  convert hlocal using 1
  · funext k z
    simp [scaledEval, family, eval_add, eval_mul, Complex.real_smul, div_eq_mul_inv]
    ring
  · funext z
    simp [scaledEval, eval_add, eval_mul]

/-- Here p indexes the extracted subsequence, and the conclusion concerns its
original, unscaled polynomials. -/
theorem quartic_normalized_escape_low_zero (p : ℕ → ℂ × ℂ) (a b : ℂ)
    (hM : Tendsto (fun j => ‖p j‖) atTop atTop)
    (hab : a ≠ 0 ∨ b ≠ 0)
    (hconv : TendstoLocallyUniformly
      (fun j z => (family 2 4 (p j).1 (p j).2).eval z / (‖p j‖ : ℂ))
      (fun z => a * (hermite 2).eval z + b * (hermite 4).eval z) atTop) :
    ∀ᶠ j in atTop, ∃ z : ℂ, (family 2 4 (p j).1 (p j).2).eval z = 0 ∧
      |z.im| < 1 / 2 := by
  let G := C a * hermite 2 + C b * hermite 4
  have hG (z : ℂ) : G.eval z = a * (hermite 2).eval z + b * (hermite 4).eval z := by
    simp [G, eval_add, eval_mul]
  have hne : (fun z => G.eval z) ≠ 0 := by
    intro h
    apply homogeneous_ne_zero hab
    apply Polynomial.funext
    intro z
    change G.eval z = (0 : Polynomial ℂ).eval z
    rw [eval_zero]
    exact congrFun h z
  obtain ⟨c,hc,hcim⟩ := quartic_homogeneous_small a b hab
  have hopen : IsOpen {w : ℂ | |w.im| < 1/2} :=
    isOpen_lt Complex.continuous_im.abs continuous_const
  obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hopen c hcim
  have hz := zeros_persist_locally _ (fun z => G.eval z)
    (fun j => (family 2 4 (p j).1 (p j).2).differentiable.div_const _)
    G.differentiable (by simpa only [hG] using hconv) hne c ((hG c).trans hc) r hr
  filter_upwards [hz, hM.eventually (eventually_gt_atTop 0)] with j hj hpos
  obtain ⟨w,hw,hroot⟩ := hj
  have hn : (‖p j‖ : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  exact ⟨w, by simpa using (div_eq_iff hn).mp hroot, hsub hw⟩

private theorem height_le_of_root (p : ℂ × ℂ) {z : ℂ}
    (hz : (family 2 4 p.1 p.2).eval z = 0) : quarticFamilyHeight p ≤ |z.im| :=
  csInf_le ⟨0, by rintro _ ⟨w,_,rfl⟩; exact abs_nonneg _⟩ ⟨z,hz,rfl⟩

private theorem le_height_of_forall_roots (p : ℂ × ℂ) {t : ℝ}
    (h : ∀ z : ℂ, (family 2 4 p.1 p.2).eval z = 0 → t ≤ |z.im|) :
    t ≤ quarticFamilyHeight p := by
  obtain ⟨w,hw,_⟩ := family_has_lowest_zero 2 4 (by decide) (by decide) p.1 p.2
  exact le_csInf ⟨_,w,hw,rfl⟩ (by rintro _ ⟨z,hz,rfl⟩; exact h z hz)

/-- The height limit contradicts the eventual low zeros along any escape. -/
theorem quartic_coefficients_bounded_of_height_limit (p : ℕ → ℂ × ℂ) (η : ℝ)
    (hη : 1 / 2 < η) (hlim : Tendsto (fun j => quarticFamilyHeight (p j)) atTop (𝓝 η)) :
    BddAbove (Set.range (fun j => ‖p j‖)) := by
  by_contra h
  obtain ⟨σ,q,hσ,hM,hunit,_,_,hconv⟩ := quartic_unbounded_normalized_subsequence p h
  have hlow := quartic_normalized_escape_low_zero (fun k => p (σ k)) q.1 q.2 hM
    (nonzero_coords_of_unit hunit) (by simpa only [eval_add, eval_mul, eval_C] using hconv)
  have hhigh := (hlim.comp hσ.tendsto_atTop).eventually (lt_mem_nhds hη)
  obtain ⟨k,⟨w,hw,hlt⟩,hgt⟩ := (hlow.and hhigh).exists
  exact (not_lt_of_ge (height_le_of_root (p (σ k)) hw)) (hlt.trans hgt)

private theorem family24_ne_zero (p : ℂ × ℂ) : family 2 4 p.1 p.2 ≠ 0 := by
  apply ne_zero_of_natDegree_gt (n := 0)
  rw [family_degree 2 4 (by decide) (by decide)]
  split_ifs <;> decide

/-- For each member choose a zero nearest the prescribed limit zero. -/
private theorem roots_along_coefficients {u : ℕ → ℂ × ℂ} {q : ℂ × ℂ}
    (hu : Tendsto u atTop (𝓝 q)) (z : ℂ) (hz : (family 2 4 q.1 q.2).eval z = 0) :
    ∃ w : ℕ → ℂ, (∀ k, (family 2 4 (u k).1 (u k).2).eval (w k) = 0) ∧
      Tendsto w atTop (𝓝 z) := by
  let P := fun t : ℂ × ℂ => family 2 4 t.1 t.2
  have hc : Continuous (fun v : (ℂ × ℂ) × ℂ => (P v.1).eval v.2) := by
    simp only [P, family, eval_add, eval_mul, eval_one, eval_C, eval_ofNat, eval_X]
    fun_prop
  have hmin (k : ℕ) : ∃ x : ℂ, (P (u k)).eval x = 0 ∧
      ∀ y : ℂ, (P (u k)).eval y = 0 → dist x z ≤ dist y z := by
    obtain ⟨x,hx,_⟩ := family_has_lowest_zero 2 4 (by decide) (by decide) (u k).1 (u k).2
    exact Set.exists_min_image {x | (P (u k)).IsRoot x} (fun x => dist x z)
      (finite_setOfPred_isRoot (family24_ne_zero (u k))) ⟨x,hx⟩
  choose w hw hnear using hmin
  refine ⟨w,hw,Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  filter_upwards [hu.eventually (nearby_polynomial_root P hc q (family24_ne_zero q) z hz ε hε)]
    with k hk
  obtain ⟨y,hy,hd⟩ := hk
  exact (hnear k y hy).trans_lt hd

/-- A subsequence of the given maximizing sequence converges to a maximizer.
Each zero of that member is approached by zeros along the same coefficient subsequence. -/
theorem quartic_maximizing_subsequence (p : ℕ → ℂ × ℂ) (η : ℝ)
    (hsup : IsLUB (Set.range quarticFamilyHeight) η)
    (hlim : Tendsto (fun j => quarticFamilyHeight (p j)) atTop (𝓝 η)) :
    ∃ (σ : ℕ → ℕ) (q : ℂ × ℂ), StrictMono σ ∧
      Tendsto (fun k => p (σ k)) atTop (𝓝 q) ∧ quarticFamilyHeight q = η ∧
      ∀ z : ℂ, (family 2 4 q.1 q.2).eval z = 0 →
        ∃ w : ℕ → ℂ, (∀ k, (family 2 4 (p (σ k)).1 (p (σ k)).2).eval (w k) = 0) ∧
          Tendsto w atTop (𝓝 z) := by
  obtain ⟨v,hv,_⟩ := quartic_upper_root
  let b := (64*v^3)⁻¹
  let a := (12-24*v^2)*b
  have hcandidate : v.im ≤ quarticFamilyHeight (a,b) :=
    le_height_of_forall_roots _ (quartic_candidate_heights v hv).1
  have hη : 1/2 < η := by
    have hsup' := hsup.1 (Set.mem_range_self (a,b))
    linarith [(quartic_root_height v hv).1]
  obtain ⟨R,hR⟩ := quartic_coefficients_bounded_of_height_limit p η hη hlim
  have hball (k : ℕ) : p k ∈ closedBall 0 R :=
    mem_closedBall_zero_iff.mpr (hR (Set.mem_range_self k))
  obtain ⟨q,_,σ,hσ,hq⟩ := (isCompact_closedBall (0 : ℂ × ℂ) R).tendsto_subseq hball
  refine ⟨σ,q,hσ,hq,le_antisymm (hsup.1 (Set.mem_range_self q)) ?_,
    roots_along_coefficients hq⟩
  apply le_height_of_forall_roots
  intro z hz
  obtain ⟨w,hw,hwlim⟩ := roots_along_coefficients hq z hz
  exact le_of_tendsto_of_tendsto' (hlim.comp hσ.tendsto_atTop)
    ((Complex.continuous_im.abs).continuousAt.tendsto.comp hwlim)
    (fun k => height_le_of_root (p (σ k)) (hw k))

#print axioms quartic_unbounded_normalized_subsequence
#print axioms quartic_normalized_escape_low_zero
#print axioms quartic_coefficients_bounded_of_height_limit
#print axioms quartic_maximizing_subsequence

end Turan
