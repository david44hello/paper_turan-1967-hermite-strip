-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

noncomputable section
namespace Turan.Generating
open Filter
open scoped Topology

def jet (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0 / n.factorial

def shift (f : ℂ → ℂ) (t : ℂ) : ℂ := t*f t
def scale (a : ℂ) (f : ℂ → ℂ) (t : ℂ) : ℂ := a*f t

def rhs (A B : ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  scale A f + shift (scale B f + scale 2 (shift (deriv f)) +
    shift (scale A f + shift (scale (-1) f + scale (-1) (shift (deriv f)))))

private theorem jet_add (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    jet (f+g) n = jet f n + jet g n := by
  simp only [jet, iteratedDeriv_add hf.contDiffAt hg.contDiffAt, add_div]

private theorem jet_scale (a : ℂ) (f : ℂ → ℂ) (n : ℕ) :
    jet (scale a f) n = a * jet f n := by
  unfold jet scale
  rw [iteratedDeriv_const_mul_field, mul_div_assoc]

private theorem jet_shift_zero (f : ℂ → ℂ) : jet (shift f) 0 = 0 := by simp [jet, shift]

private theorem jet_shift_succ (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    jet (shift f) (n+1) = jet f n := by
  unfold jet shift
  rw [iteratedDeriv_fun_mul (f := fun x : ℂ => x) (g := f) (by fun_prop) hf.contDiffAt]
  simp only [iteratedDeriv_fun_id_zero, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' _ 1]
  simp [Nat.factorial_succ, Nat.cast_add_one_ne_zero, div_eq_mul_inv,
    mul_comm, mul_left_comm]

private theorem jet_deriv (f : ℂ → ℂ) (n : ℕ) :
    jet (deriv f) n = ((n:ℂ)+1) * jet f (n+1) := by
  rw [jet, jet, iteratedDeriv_succ', Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp

private theorem jet_euler (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    jet (shift (deriv f)) n = (n:ℂ)*jet f n := by
  cases n with
  | zero => simp [jet_shift_zero]
  | succ n => rw [jet_shift_succ _ hf.deriv, jet_deriv, Nat.cast_succ]

/-- Coefficient comparison in the logarithmic derivative equation, written in
nested powers of the parameter so that low indices never require subtraction. -/
theorem jet_recurrences (f : ℂ → ℂ) (A B : ℂ) (hf : AnalyticAt ℂ f 0)
    (he : deriv f =ᶠ[𝓝 0] rhs A B f) :
    jet f 1 = A*jet f 0 ∧
    2*jet f 2 = A*jet f 1 + B*jet f 0 ∧
    3*jet f 3 = A*jet f 2 + (B+2)*jet f 1 + A*jet f 0 ∧
    ∀ n : ℕ, ((n:ℂ)+4)*jet f (n+4) = A*jet f (n+3) +
      (B+2*((n:ℂ)+2))*jet f (n+2) + A*jet f (n+1) - ((n:ℂ)+1)*jet f n := by
  have h (n : ℕ) : ((n:ℂ)+1)*jet f (n+1) = jet (rhs A B f) n := by
    rw [← jet_deriv, jet, jet, he.iteratedDeriv_eq]
  have hs {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) : AnalyticAt ℂ (shift g) 0 := analyticAt_id.mul hg
  have hc (a : ℂ) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) : AnalyticAt ℂ (scale a g) 0 := analyticAt_const.mul hg
  have ha₁ := hc (-1) hf |>.add (hc (-1) (hs hf.deriv))
  have ha₂ := (hc A hf).add (hs ha₁)
  have ha₃ := ((hc B hf).add (hc 2 (hs hf.deriv))).add (hs ha₂)
  have ha₄ := (hc B hf).add (hc 2 (hs hf.deriv))
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e := h 0
    simpa [rhs, jet_add _ _ (hc A hf) (hs ha₃), jet_scale, jet_shift_zero] using e
  · have e := h 1
    simp only [rhs, jet_add _ _ (hc A hf) (hs ha₃), jet_shift_succ _ ha₃,
      jet_add _ _ ha₄ (hs ha₂), jet_add _ _ (hc B hf) (hc 2 (hs hf.deriv)), jet_scale, jet_euler _ hf,
      jet_shift_zero, Nat.cast_one, Nat.cast_zero] at e
    linear_combination e
  · have e := h 2
    simp only [rhs, jet_add _ _ (hc A hf) (hs ha₃), jet_shift_succ _ ha₃,
      jet_add _ _ ha₄ (hs ha₂), jet_add _ _ (hc B hf) (hc 2 (hs hf.deriv)),
      jet_shift_succ _ ha₂, jet_add _ _ (hc A hf) (hs ha₁),
      jet_scale, jet_euler _ hf,
      jet_shift_zero, Nat.cast_ofNat, Nat.cast_one] at e
    linear_combination e
  · intro n
    have e := h (n+3)
    simp only [rhs, jet_add _ _ (hc A hf) (hs ha₃), jet_shift_succ _ ha₃,
      jet_add _ _ ha₄ (hs ha₂), jet_add _ _ (hc B hf) (hc 2 (hs hf.deriv)),
      jet_shift_succ _ ha₂, jet_add _ _ (hc A hf) (hs ha₁), jet_shift_succ _ ha₁,
      jet_add _ _ (hc (-1) hf) (hc (-1) (hs hf.deriv)), jet_scale, jet_euler _ hf,
      Nat.cast_add, Nat.cast_ofNat] at e
    linear_combination e

end Turan.Generating
