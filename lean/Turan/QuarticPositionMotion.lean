module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.QuarticPositionAlgebra

@[expose] public section

noncomputable section
open Filter Topology
namespace Turan.QuarticPosition

private def H (z : ℂ) := 12*z-2
private def J (z : ℂ) := 12*z^2+4*z-2
private def F (z : ℂ) := 12*z^4+16*z^3+12*z^2-3
/-- Determinant of the real linear system for the two coefficients of the centered cubic. -/
private def det (z : ℂ) := (J z).im*(H z).re-(J z).re*(H z).im
private def L (z : ℂ) := ((F z).im*(H z).re-(F z).re*(H z).im)/det z
private def K (z : ℂ) := ((F z).im*(J z).re-(F z).re*(J z).im)/det z
private def lin (z : ℂ) := 8*z^3-2*z*(L z : ℂ)-(K z : ℂ)
private def disc (z : ℂ) := 4*L z^3-27*K z^2

private theorem det_pos {z : ℂ} (hz : 0 < z.im) : 0 < det z := by
  have e : det z = z.im*((12*z.re-2)^2+(12*z.im)^2+12) := by
    norm_num [det,H,J,pow_succ,Complex.mul_re,Complex.mul_im]; ring
  rw [e]
  positivity

private theorem solves {z : ℂ} (hz : 0 < z.im) :
    H z*(K z : ℂ) = J z*(L z : ℂ)-F z := by
  apply Complex.ext <;> simp [L,K,Complex.mul_re,Complex.mul_im] <;>
    field_simp [(det_pos hz).ne'] <;> unfold det <;> ring

private theorem unique_pair {z : ℂ} {l k : ℝ} (hz : 0 < z.im)
    (h : H z*(k:ℂ) = J z*(l:ℂ)-F z) : L z=l ∧ K z=k := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [Complex.mul_re,Complex.mul_im] at hr hi
  constructor
  · apply (div_eq_iff (det_pos hz).ne').2
    unfold det
    linear_combination (H z).re*hi-(H z).im*hr
  · apply (div_eq_iff (det_pos hz).ne').2
    unfold det
    linear_combination (J z).re*hi-(J z).im*hr

/-- A depressed real cubic of positive discriminant has only real complex roots. -/
private theorem cubic_real {l k : ℝ} {v : ℂ} (hd : 0 < 4*l^3-27*k^2)
    (hv : v^3-(l:ℂ)*v-(k:ℂ)=0) : v.im=0 := by
  by_contra hn
  have hr := congrArg Complex.re hv
  have hi := congrArg Complex.im hv
  norm_num [pow_succ,Complex.mul_re,Complex.mul_im] at hr hi
  have hl : l = 3*v.re^2-v.im^2 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show v.im*(l-(3*v.re^2-v.im^2))=0 by linear_combination -hi)).resolve_left hn
  have hk : k = -2*v.re*(v.re^2+v.im^2) := by rw [hl] at hr; linear_combination -hr
  have e : 4*l^3-27*k^2 = -4*v.im^2*(9*v.re^2+v.im^2)^2 := by rw [hl,hk]; ring
  rw [e] at hd
  nlinarith only [hd, mul_nonneg (sq_nonneg v.im) (sq_nonneg (9*v.re^2+v.im^2))]

private theorem move {α : ℂ} (hα : 0 < α.im) (hd : 0 < disc α) (hc : lin α ≠ 0) :
    ∃ A : ℂ, α.im < A.im ∧ 0 < disc A ∧ lin A ≠ 0 := by
  have hd₀ := (det_pos hα).ne'
  have hdet : ContinuousAt det α := by unfold det J H; fun_prop
  have hL : ContinuousAt L α := by
    unfold L
    apply ContinuousAt.div _ hdet hd₀
    unfold F H
    fun_prop
  have hK : ContinuousAt K α := by
    unfold K
    apply ContinuousAt.div _ hdet hd₀
    unfold F J
    fun_prop
  have hd' : ContinuousAt disc α := by unfold disc; fun_prop
  have hc' : ContinuousAt lin α := by unfold lin; fun_prop
  have hgood := (hd'.eventually (lt_mem_nhds hd)).and (hc'.eventually_ne hc)
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hgood
  let A := α + (δ/2 : ℝ)*Complex.I
  have hdist : dist A α < δ := by
    rw [dist_eq_norm]; simp [A,abs_of_pos hδ]; linarith
  refine ⟨A, ?_, hball hdist⟩
  simp [A, Complex.mul_im]; linarith

/-- Moving the mean of three distinct upper contacts would increase the extremal height. -/
theorem upper_repeat {a b p q r s : ℂ} {y : ℝ} (hb : b ≠ 0) (hy : 0 < y)
    (hmax : ∀ c d : ℂ, ∃ z : ℂ, (family 2 4 c d).eval z=0 ∧ |z.im|≤y)
    (hf : Factors a b p q r s) (hp : p.im=y) (hq : q.im=y) (hr : r.im=y) :
    p=q ∨ p=r ∨ q=r := by
  by_contra! hn
  let α := (p+q+r)/3
  let t := p.re-α.re
  let u := q.re-α.re
  let v := r.re-α.re
  let l := -(t*u+t*v+u*v)
  let k := t*u*v
  have hα : α.im=y := by simp [α,hp,hq,hr]; ring
  have hsum : t+u+v=0 := by simp [t,u,v,α]; ring
  have ep : p=α+(t:ℂ) := by apply Complex.ext <;> simp [t,hp,hα]
  have eq : q=α+(u:ℂ) := by apply Complex.ext <;> simp [u,hq,hα]
  have er : r=α+(v:ℂ) := by apply Complex.ext <;> simp [v,hr,hα]
  have es : s= -3*α := by dsimp [α]; linear_combination roots_sum hb hf
  have ev : v= -(t+u) := by linarith
  have hne₁ : t ≠ u := fun h => hn.1 (by rw [ep,eq,h])
  have hne₂ : t ≠ v := fun h => hn.2.1 (by rw [ep,er,h])
  have hne₃ : u ≠ v := fun h => hn.2.2 (by rw [eq,er,h])
  have hd : 0 < 4*l^3-27*k^2 := by
    have he : 4*l^3-27*k^2 = (t-u)^2*(t-v)^2*(u-v)^2 := by dsimp [l,k]; rw [ev]; ring
    rw [he]
    exact mul_pos (mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hne₁))
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hne₂))) (sq_pos_of_ne_zero (sub_ne_zero.mpr hne₃))
  have ⟨hcon, hlin⟩ := constraint (a:=a) hb (c₂ := -6*α^2-(l:ℂ))
    (c₁ := 8*α^3-2*α*(l:ℂ)-(k:ℂ)) (c₀ := -3*α^4+3*α^2*(l:ℂ)-3*α*(k:ℂ))
    (fun z => by rw [hf z,ep,eq,er,es]; dsimp only [l,k]; rw [ev]; push_cast; ring)
  have hpos : 0 < α.im := hα.symm ▸ hy
  have ⟨hL,hK⟩ := unique_pair hpos (l:=l) (k:=k) (by unfold H J F; linear_combination -hcon)
  obtain ⟨A,hA,hdisc,hc⟩ := move hpos (by simpa [disc,hL,hK] using hd)
    (by simpa [lin,hL,hK] using hlin)
  have ha := solves (hpos.trans hA)
  obtain ⟨c,d,hd',hfac⟩ := realize (c₂ := -6*A^2-(L A : ℂ)) (c₁ := lin A)
    (c₀ := -3*A^4+3*A^2*(L A : ℂ)-3*A*(K A : ℂ)) (by
      unfold H J F at ha; unfold lin; linear_combination -ha) hc
  obtain ⟨z,hz,hzy⟩ := hmax c d
  rw [eval_model,hfac] at hz
  have he : ((z-A)^3-(L A : ℂ)*(z-A)-(K A : ℂ))*(z+3*A)=0 := by
    convert (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hd') using 1
    unfold lin
    ring
  rw [abs_le] at hzy
  rcases mul_eq_zero.mp he with hu | hl
  · have h := cubic_real hdisc hu
    rw [Complex.sub_im] at h
    linarith
  · have h := congrArg Complex.im hl
    norm_num [Complex.mul_im] at h
    linarith

end Turan.QuarticPosition
