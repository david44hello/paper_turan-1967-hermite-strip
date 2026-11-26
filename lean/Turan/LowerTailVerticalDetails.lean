module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Turan.LowerTailRealEnergy
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.ODE.Gronwall

@[expose] public section

noncomputable section
open Filter Metric Set Polynomial
open scoped ComplexConjugate Topology Matrix
namespace Turan.LowerTailSteps

def modeVector (m : ℕ) (z : ℂ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![psi m z, deriv (psi m) z / (Real.sqrt (2*(m:ℝ)) : ℂ)]

def verticalMatrix (m : ℕ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let s : ℂ := Real.sqrt (2*(m:ℝ))
  !![0, s; -s, 2*z]

private abbrev pair (a b : ℂ) : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![a,b]

private theorem pair_sq (a b : ℂ) : ‖pair a b‖^2 = ‖a‖^2 + ‖b‖^2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, pair]

private theorem vec_sq (m : ℕ) (X : ℝ) : ‖modeVector m X‖^2 = realEnergy m X := by
  rw [modeVector, pair_sq, realEnergy, norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, Real.sq_sqrt (by positivity)]

private theorem pair_le (a b : ℂ) : ‖a‖ ≤ ‖pair a b‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [pair_sq]; nlinarith only [sq_nonneg ‖b‖])

private theorem pair_hasDeriv {f g : ℝ → ℂ} {x : ℝ} {a b : ℂ}
    (hf : HasDerivAt f a x) (hg : HasDerivAt g b x) :
    HasDerivAt (fun t => pair (f t) (g t)) (pair a b) x := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℂ)).symm
  have H : HasDerivAt (fun t => ![f t,g t]) ![a,b] x := hasDerivAt_pi.mpr (fun i => by
    fin_cases i
    · exact hf
    · exact hg)
  exact L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x H

private theorem mat_apply (m : ℕ) (z : ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (verticalMatrix m z) v =
      pair ((Real.sqrt (2*(m:ℝ)):ℂ)*v 1) (-(Real.sqrt (2*(m:ℝ)):ℂ)*v 0 + 2*z*v 1) := by
  change WithLp.toLp 2 ((verticalMatrix m z) *ᵥ (WithLp.ofLp v)) = _
  ext i
  fin_cases i <;> simp [verticalMatrix, pair, Matrix.mulVec, dotProduct, Fin.sum_univ_two]


theorem real_segment (m : ℕ) (hm : 1 ≤ m) (X : ℝ) (hX : |X| ≤ 2) :
    realEnergy m X ≤ Real.exp (2*X^2) ∧ Real.exp (2*X^2) ≤ Real.exp 8 ∧
    ‖modeVector m (X : ℂ)‖ = Real.sqrt (realEnergy m X) ∧
    ‖modeVector m (X : ℂ)‖ ≤ Real.exp 4 := by
  have he := (realEnergy_comparison m hm).2.2 X
  have hub := (energy_origin_bounds m hm).2
  have h1 : realEnergy m X ≤ Real.exp (2*X^2) := he.trans (mul_le_of_le_one_left (Real.exp_nonneg _) hub)
  have h2 : Real.exp (2*X^2) ≤ Real.exp 8 := Real.exp_le_exp.mpr (by
    have h := (sq_le_sq₀ (abs_nonneg X) (by norm_num : (0:ℝ) ≤ 2)).mpr hX
    rw [sq_abs] at h
    linarith)
  have h3 : ‖modeVector m (X:ℂ)‖ = Real.sqrt (realEnergy m X) := by rw [← vec_sq,Real.sqrt_sq (norm_nonneg _)]
  refine ⟨h1,h2,h3, ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg _)).mp
  rw [vec_sq, sq, ← Real.exp_add]
  exact_mod_cast h1.trans h2

theorem vertical_operator (m : ℕ) (hm : 1 ≤ m) (z : ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (verticalMatrix m z)‖ ≤ Real.sqrt (2*(m:ℝ)) + 2*‖z‖ := by
  let f := Real.sqrt (2*(m:ℝ))
  have hf : 0 ≤ f := Real.sqrt_nonneg _
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  let w := pair (v 1) (-v 0)
  have hw : ‖w‖ = ‖v‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [show ‖w‖^2 = ‖v 1‖^2+‖-v 0‖^2 from pair_sq .., EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, norm_neg, add_comm]
  have hb : ‖v 1‖ ≤ ‖v‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    linarith only [sq_nonneg ‖v 0‖]
  have hid : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (verticalMatrix m z) v =
      (f:ℂ) • w + pair 0 (2*z*v 1) := by
    rw [mat_apply]
    ext i
    fin_cases i <;> simp [w,pair,f] <;> ring
  have hn : ‖pair 0 (2*z*v 1)‖ = ‖2*z*v 1‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [pair_sq]
  rw [hid]
  apply (norm_add_le ..).trans
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs, abs_of_nonneg hf,hw,hn]
  simp only [norm_mul,Complex.norm_ofNat]
  change _ ≤ (f+2*‖z‖)*‖v‖
  nlinarith only [mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*‖z‖ by positivity)]

theorem vertical_segment (m : ℕ) (hm : 1 ≤ m) (c : ℂ)
    (hX : |c.re| ≤ 2) (hY : |c.im| < 76/100) :
    (∀ s ∈ Icc (0 : ℝ) 1, ‖(c.re : ℂ) + (s*c.im : ℝ)*Complex.I‖ < 214/100) ∧
    ‖modeVector m c‖ ≤ ‖modeVector m (c.re : ℂ)‖ *
      Real.exp ((Real.sqrt (2*(m:ℝ)) + 428/100) * |c.im|) := by
  let b := (c.im:ℂ)*Complex.I
  let z (s : ℂ) := (c.re:ℂ)+s*b
  have hz (s : ℂ) : HasDerivAt z b s := by simpa [z] using ((hasDerivAt_id s).mul_const b).const_add (c.re:ℂ)
  have hbound (s : ℝ) (hs : s ∈ Icc 0 1) : ‖z s‖ < 214/100 := by
    have hi : |s*c.im| ≤ |c.im| := by rw [abs_mul,abs_of_nonneg hs.1]; exact mul_le_of_le_one_left (abs_nonneg _) hs.2
    apply (sq_lt_sq₀ (norm_nonneg _) (by norm_num)).mp
    have hr := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).mpr hX
    have hy := (sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 76/100)).mpr (hi.trans_lt hY)
    rw [sq_abs] at hr hy
    simp [Complex.sq_norm,Complex.normSq_apply,z,b,Complex.add_re,Complex.add_im,
      Complex.mul_re,Complex.mul_im]
    nlinarith only [hr,hy]
  refine ⟨fun s hs => ?_, ?_⟩
  · convert hbound s hs using 2 <;> dsimp [z,b] <;> push_cast <;> ring
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  let f := Real.sqrt (2*((j:ℝ)+1))
  have hf : 0 < f := Real.sqrt_pos.mpr (by positivity)
  have hvec (w : ℂ) : modeVector (j+1) w = pair (psi (j+1) w) (psi j w) := by
    unfold modeVector
    simp only [Nat.cast_succ, ((psi_adjacent_derivatives j w).1).deriv]
    change pair _ ((f:ℂ)*psi j w/(f:ℂ)) = _
    rw [mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hf.ne')]
  let V (s : ℝ) := modeVector (j+1) (z s)
  let V' (s : ℝ) := b • (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (verticalMatrix (j+1) (z s)) (V s))
  have hd (s : ℝ) : HasDerivAt V (V' s) s := by
    obtain ⟨hP,hQ⟩ := psi_adjacent_derivatives j (z s)
    convert pair_hasDeriv ((hP.comp (s:ℂ) (hz s)).comp_ofReal)
      ((hQ.comp (s:ℂ) (hz s)).comp_ofReal) using 1
    · funext u; exact hvec _
    · dsimp only [V',V]; rw [mat_apply,hvec,Nat.cast_succ]
      ext i
      fin_cases i <;> simp [pair] <;> ring
  let K := (f+428/100)*|c.im|
  have rate (s : ℝ) (hs : s ∈ Ico 0 1) : ‖V' s‖ ≤ K*‖V s‖ + 0 := by
    have h := (vertical_operator (j+1) (by omega) (z s))
    rw [Nat.cast_succ] at h
    have hz' := hbound s ⟨hs.1,hs.2.le⟩
    have hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (verticalMatrix (j+1) (z s))‖ ≤ f+428/100 := by
      dsimp [f]; linarith
    dsimp only [V',K]
    rw [norm_smul, show ‖b‖ = |c.im| by simp [b], add_zero, mul_comm (f+_)]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have H := norm_le_gronwallBound_of_norm_deriv_right_le
    (fun s _ => (hd s).continuousAt.continuousWithinAt) (fun s _ => (hd s).hasDerivWithinAt)
    (le_refl ‖V 0‖) rate 1 (by simp)
  simpa [V,z,b,K,f,gronwallBound_ε0, Complex.re_add_im] using H

theorem lower_vertical_chain (m : ℕ) (hm : 1 ≤ m) (c : ℂ)
    (hX : |c.re| ≤ 2) (hY : |c.im| < 76/100) :
    realEnergy m c.re ≤ Real.exp (2*c.re^2) ∧
    ‖psi m c‖ ≤ ‖modeVector m c‖ ∧
    ‖modeVector m c‖ ≤ Real.exp 4 * Real.exp ((76/100)*Real.sqrt (2*(m:ℝ))+326/100) ∧
    Real.exp 4 * Real.exp ((76/100)*Real.sqrt (2*(m:ℝ))+326/100) <
      Real.exp (8+(76/100)*Real.sqrt (2*(m:ℝ))) := by
  have H := real_segment m hm c.re hX
  have V := (vertical_segment m hm c hX hY).2
  have he : (Real.sqrt (2*(m:ℝ))+428/100)*|c.im| ≤ (76/100)*Real.sqrt (2*(m:ℝ))+326/100 := by
    nlinarith only [mul_le_mul_of_nonneg_left hY.le (show 0 ≤ Real.sqrt (2*(m:ℝ))+428/100 by positivity), hY.le]
  refine ⟨H.1,pair_le .., V.trans (mul_le_mul H.2.2.2 (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) (Real.exp_nonneg _)),?_⟩
  rw [← Real.exp_add,Real.exp_lt_exp]
  linarith

end Turan.LowerTailSteps
