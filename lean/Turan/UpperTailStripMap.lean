module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailStripFactors
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

noncomputable section
open Set
namespace Turan.UpperTailStrip

def stripTanh (s : ℝ) (z : ℂ) : ℂ :=
  Complex.tanh ((Real.pi : ℂ)*(z-(s:ℂ))/(4*(TailStrip.height : ℂ)))

private def rate : ℝ := 11*Real.pi/14
private theorem rate_pos : 0 < rate := by unfold rate; positivity
private theorem rate_height : rate*TailStrip.height = Real.pi/2 := by
  unfold rate TailStrip.height; ring

private theorem kernel_eq (s : ℝ) (z : ℂ) : stripTanh s z = TailStrip.factor s z := by
  let t := (Real.pi : ℂ)*(z-(s:ℂ))/(4*(TailStrip.height : ℂ))
  have he : t+t = (rate:ℂ)*(z-s) := by
    simp only [t,rate,TailStrip.height, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    ring
  change Complex.tanh t = (Complex.exp ((rate:ℂ)*(z-s))-1)/(Complex.exp ((rate:ℂ)*(z-s))+1)
  rw [Complex.tanh, Complex.sinh, Complex.cosh, div_div_div_cancel_right₀ two_ne_zero,
    ← mul_div_mul_right _ _ (Complex.exp_ne_zero t), sub_mul, add_mul, ← Complex.exp_add,
    ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, he]

private theorem cayley_right {w : ℂ} (hw : ‖w‖ < 1) : 0 < ((1+w)/(1-w)).re := by
  have hne : 1-w ≠ 0 := sub_ne_zero.mpr (fun he => by simp [← he] at hw)
  have hs := (sq_lt_sq₀ (norm_nonneg w) zero_le_one).mpr hw
  rw [Complex.sq_norm, Complex.normSq_apply] at hs
  rw [Complex.div_re, ← add_div]
  apply div_pos _ (Complex.normSq_pos.mpr hne)
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, zero_add, zero_sub]
  nlinarith only [hs]

theorem strip_tanh_image (s : ℝ) :
    stripTanh s '' {z : ℂ | |z.im| < TailStrip.height} = Metric.ball (0:ℂ) 1 ∧
    (∀ z ∈ TailStrip.strip, TailStrip.factor s z = stripTanh s z ∧
      (stripTanh s z = 0 ↔ z = (s:ℂ))) ∧
    (∀ z : ℂ, |z.im| = TailStrip.height → ‖stripTanh s z‖ = 1) := by
  refine ⟨Set.ext fun w => ⟨?_, ?_⟩, ?_, fun z hz => (congrArg norm (kernel_eq s z)).trans (TailStrip.factor_line s hz)⟩
  · rintro ⟨z,hz,rfl⟩
    rw [Metric.mem_ball, dist_zero_right, kernel_eq]
    let E := Complex.exp ((rate:ℂ)*(z-s))
    have him : |rate*z.im| < Real.pi/2 := by
      rw [abs_mul,abs_of_pos rate_pos, ← rate_height]
      exact mul_lt_mul_of_pos_left hz rate_pos
    have hRe : 0 < E.re := by
      simp only [E,Complex.exp_re]
      apply mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ?_)
      simpa using abs_lt.mp him
    have hlt : ‖E-1‖ < ‖E+1‖ := by
      apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
        Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,add_zero,sub_zero]
      nlinarith only [hRe]
    change ‖(E-1)/(E+1)‖ < 1
    rw [norm_div,div_lt_one (lt_of_le_of_lt (norm_nonneg _) hlt)]
    exact hlt
  · intro hw
    rw [Metric.mem_ball,dist_zero_right] at hw
    let q := (1+w)/(1-w)
    have hq : 0 < q.re := cayley_right hw
    have hq0 : q ≠ 0 := fun h => by simpa [h] using hq
    have hr : (rate:ℂ) ≠ 0 := by exact_mod_cast rate_pos.ne'
    let z := (s:ℂ) + Complex.log q/(rate:ℂ)
    refine ⟨z, ?_, ?_⟩
    · change |z.im| < TailStrip.height
      simp only [z, Complex.add_im, Complex.ofReal_im, zero_add, Complex.div_ofReal_im, Complex.log_im,
        abs_div, abs_of_pos rate_pos]
      rw [div_lt_iff₀ rate_pos, mul_comm, rate_height]
      exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hq)
    · have harg : (rate:ℂ)*(z-s) = Complex.log q := by dsimp [z]; field_simp; ring
      rw [kernel_eq]
      change (Complex.exp ((rate:ℂ)*(z-s))-1)/(Complex.exp ((rate:ℂ)*(z-s))+1) = w
      rw [harg, Complex.exp_log hq0]
      have hne : 1-w ≠ 0 := sub_ne_zero.mpr (fun he => by simp [← he] at hw)
      have hne' : q+1 ≠ 0 := by
        intro h
        have he := congrArg Complex.re h
        simp at he
        linarith
      apply (div_eq_iff hne').mpr
      dsimp [q]
      field_simp
      <;> ring
  · intro z hz
    refine ⟨(kernel_eq s z).symm, ⟨?_, ?_⟩⟩
    · intro h
      by_contra hn
      exact TailStrip.factor_ne s hz hn ((kernel_eq s z).symm.trans h)
    · rintro rfl
      simp [stripTanh]

end Turan.UpperTailStrip
