module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.QuarticPositionAlgebra

@[expose] public section

noncomputable section
namespace Turan.QuarticPosition

/-- The real and imaginary parts of the coefficient constraint exclude two contacts on each line. -/
private theorem balanced_arithmetic (β σ Y : ℝ) (hσ : 0 ≤ σ) (hY : 2 < Y)
    (he : σ^2*(β^2-2*β+2+Y) = β^2-4*β+6+2*Y)
    (hu : 2*σ*|β| ≤ 2*β+σ^2-Y-2) : False := by
  let D := β^2-2*β+2+Y
  have hD : 1+Y ≤ D := by dsimp [D]; nlinarith [sq_nonneg (β-1)]
  have hD0 : 0 < D := by linarith
  have h₂ : (σ^2-2)*D = 2-β^2 := by dsimp [D]; linear_combination he
  have h₁ : (1-σ^2)*D = 2*β-4-Y := by dsimp [D]; linear_combination -he
  have hx : σ^2 < Y+2 := by
    by_contra! h
    nlinarith [mul_nonneg (show 0 ≤ σ^2-2-Y by linarith) hD0.le,
      mul_nonneg (show 0 ≤ Y-2 by linarith) hD0.le, sq_nonneg β]
  have hb : 0 < β := by nlinarith [mul_nonneg hσ (abs_nonneg β)]
  rw [abs_of_pos hb] at hu
  have hs : σ < 1 := by
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) hb.le]
  have hlow : (4-σ^2)*(1+σ) ≥ 4 := by
    have hsq : σ^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hs.le) (show 0 ≤ 1+σ by linarith)]
    nlinarith [mul_nonneg hσ (show 0 ≤ 4-σ-σ^2 by linarith)]
  have hlt : 4 < (Y+2-σ^2)*(1+σ) := by
    nlinarith [mul_pos (sub_pos.mpr hY) (show 0 < 1+σ by linarith)]
  have hupper := mul_le_mul_of_nonneg_right
    (show Y+2-σ^2 ≤ 2*β*(1-σ) by linarith) (show 0 ≤ (1+σ)*D by positivity)
  have hbad : 4*D < 2*β*(2*β-4-Y) := calc
    4*D < ((Y+2-σ^2)*(1+σ))*D := mul_lt_mul_of_pos_right hlt hD0
    _ ≤ 2*β*((1-σ^2)*D) := by linarith only [hupper]
    _ = _ := by rw [h₁]
  dsimp [D] at hbad
  nlinarith [mul_pos hb (show 0 < Y by linarith)]

theorem balanced_impossible {a b p q r s : ℂ} {y : ℝ} (hb : b ≠ 0)
    (hy : 4/5 < y) (hf : Factors a b p q r s)
    (hp : p.im=y) (hq : q.im=y) (hr : r.im= -y) (hs : s.im= -y) : False := by
  let α := (p+q)/2
  let t := (p.re-q.re)/2
  let u := (r.re-s.re)/2
  let U := t^2+u^2
  let V := t^2-u^2
  have hsum := roots_sum hb hf
  have hreal := congrArg Complex.re hsum
  simp only [Complex.add_re, Complex.zero_re] at hreal
  have hα : α.im = y := by simp [α,hp,hq]
  have ep : p = α+(t:ℂ) := by apply Complex.ext <;> simp [α,t,hp,hq]; ring
  have eq : q = α-(t:ℂ) := by apply Complex.ext <;> simp [α,t,hp,hq]; ring
  have er : r = -α+(u:ℂ) := by apply Complex.ext <;> simp [α,u,hp,hq,hr]; linarith
  have es : s = -α-(u:ℂ) := by apply Complex.ext <;> simp [α,u,hp,hq,hs]; linarith
  have hc := (constraint (a:=a) hb (c₂ := -2*α^2-(U:ℂ)) (c₁ := -2*α*(V:ℂ))
    (c₀ := α^4-α^2*(U:ℂ)+((U:ℂ)^2-(V:ℂ)^2)/4) (fun z => by
      rw [hf z,ep,eq,er,es]; dsimp [U,V]; push_cast; ring)).1
  let x := α.re
  let β := 1+U-2*x^2+2*y^2
  have him := congrArg Complex.im hc
  have hre := congrArg Complex.re hc
  norm_num [pow_succ,Complex.mul_im,Complex.mul_re,hα] at him hre
  have hv : V = 2*x*β := by
    have : y*(V-2*x*β)=0 := by dsimp [β,x]; linear_combination him/4
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (by linarith))
  apply balanced_arithmetic β |2*x| (4*y^2) (abs_nonneg _)
    (by nlinarith [sq_nonneg (y-4/5)])
  · rw [sq_abs]
    have h := hre
    rw [hv] at h
    dsimp [β,x] at h ⊢
    linear_combination -h
  · have huv : |V| ≤ U := abs_le.mpr (by dsimp [U,V]; constructor <;> nlinarith [sq_nonneg t,sq_nonneg u])
    rw [hv, abs_mul] at huv
    rw [sq_abs]
    dsimp [β]
    linarith

end Turan.QuarticPosition
