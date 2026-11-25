-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Small34CertificateData
import Turan.Small34SignDefs

noncomputable section
open Complex
open scoped ComplexConjugate
namespace Turan.Small34Certificate

private def gi (z : Gaussian) : ℂ := ⟨z.1,z.2⟩

private def horner {α : Type} (f : α → ℂ) (x : ℝ) : List α → ℂ
  | [] => 0
  | h :: t => f h + (x:ℂ) * horner f x t

private abbrev rowVal (t : ℝ) := horner gi t
private abbrev val (x t : ℝ) := horner (rowVal t) x

private theorem horner_add {α : Type} (op : α → α → α) (f : α → ℂ)
    (hf : ∀ a b, f (op a b) = f a + f b) (x : ℝ) (p q : List α) :
    horner f x (Small56.Certificate.addWith op p q) = horner f x p + horner f x q := by
  induction p generalizing q with
  | nil => simp [Small56.Certificate.addWith, horner]
  | cons a p ih =>
    cases q <;> simp [Small56.Certificate.addWith, horner, hf, ih]; ring

private theorem horner_map {α : Type} (op : α → α) (f : α → ℂ) (m : ℂ)
    (hf : ∀ a, f (op a) = m * f a) (x : ℝ) (p : List α) :
    horner f x (p.map op) = m * horner f x p := by
  induction p with
  | nil => simp [horner]
  | cons a p ih => simp [horner, hf, ih]; ring

private theorem gi_add (z w : Gaussian) : gi (gadd z w) = gi z + gi w := by
  apply Complex.ext <;> simp [gi, gadd]

private theorem gi_mul (a c : ℤ) (z : Gaussian) :
    gi (gmul a c z) = ((a:ℂ)+(c:ℂ)*I)*gi z := by
  apply Complex.ext <;> simp [gi, gmul, Complex.mul_re, Complex.mul_im]; ring

private theorem ev_add (t : ℝ) (p q : Row) : rowVal t (rowAdd p q) = rowVal t p + rowVal t q :=
  horner_add _ _ gi_add _ _ _

private theorem val_add (x t : ℝ) (p q : Table) :
    val x t (tableAdd p q) = val x t p + val x t q :=
  horner_add _ _ (ev_add t) _ _ _

private theorem row_shift (a c d : ℤ) (p : Row) (t : ℝ) :
    rowVal t (shiftRow a c d p) = ((a:ℂ)+((c:ℂ)+d*(t:ℂ))*I)*rowVal t p := by
  unfold shiftRow
  rw [ev_add]
  change horner gi t _ + (gi (0,0) + (t:ℂ)*horner gi t _) = _
  rw [horner_map _ _ _ (gi_mul a c), horner_map _ _ _ (gi_mul 0 d)]
  have hz : gi (0,0) = 0 := by apply Complex.ext <;> simp [gi]
  rw [hz]
  simp only [Int.cast_zero]
  change _ = _ * horner gi t p
  ring

def line (e σ : ℤ) (X V Y : ℝ) : ℂ :=
  7*((X:ℂ)-(e:ℂ)*V)+(σ:ℂ)*Y*V*I

def pair (l r σ : ℤ) (X V Y : ℝ) : ℂ := line r σ X V Y * line l (-σ) X V Y

def product (P : Boxes) (X V Y : ℝ) : ℂ :=
  pair P.l₁ P.r₁ 1 X V Y ^ 5 * pair P.l₂ P.r₂ (-1) X V Y ^ 4 *
    pair P.l₃ P.r₃ 1 X V Y ^ 2

private theorem val_endpoint (a b v e σ : ℤ) (p : Table) (x t : ℝ) :
    val x t (endpoint a b v e σ p) =
      line e σ (a+b*x) (1+v*x) (5000000+t) * val x t p := by
  unfold endpoint
  rw [val_add]
  change horner (rowVal t) x _ + (0+(x:ℂ)*horner (rowVal t) x _) = _
  rw [horner_map _ _ _ (fun p => row_shift _ _ _ p t),
      horner_map _ _ _ (fun p => row_shift _ _ _ p t)]
  unfold line
  change _ = _ * horner (rowVal t) x p
  push_cast
  ring

private theorem val_copies (a b v l r σ : ℤ) (p : Table) (n : ℕ) (x t : ℝ) :
    val x t (copies a b v l r σ p n) =
      pair l r σ (a+b*x) (1+v*x) (5000000+t) ^ n * val x t p := by
  induction n with
  | zero => simp [copies]
  | succ n ih => rw [copies,val_endpoint,val_endpoint,ih,pow_succ]; unfold pair; ring

private theorem val_table (P : Boxes) (a b v : ℤ) (x t : ℝ) :
    val x t (table P a b v) = product P (a+b*x) (1+v*x) (5000000+t) := by
  unfold table
  rw [val_copies,val_copies,val_copies]
  have h : val x t [[(1,0)]] = 1 := by apply Complex.ext <;> simp [val,rowVal,horner,gi]
  rw [h]
  unfold product
  ring

def weight (k : ℤ) (z : ℂ) : ℝ := z.re-(k:ℝ)*z.im

private theorem weight_step (k : ℤ) (a b : ℂ) (x : ℝ) :
    weight k (a+(x:ℂ)*b) = weight k a + x * weight k b := by
  simp [weight]; ring

private theorem horner_nonneg {α : Type} (f : α → ℂ) (k : ℤ) (test : α → Bool)
    (hf : ∀ a, test a = true → 0 ≤ weight k (f a))
    (x : ℝ) (hx : 0 ≤ x) (p : List α) (h : p.all test = true) :
    0 ≤ weight k (horner f x p) := by
  induction p with
  | nil => simp [horner,weight]
  | cons a p ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [horner, weight_step]
    exact add_nonneg (hf a h.1) (mul_nonneg hx (ih h.2))

theorem chart (P : Boxes) {a b v : ℤ} (h : test P a b v = true) {x t : ℝ}
    (hx : 0 ≤ x) (ht : 0 ≤ t) :
    0 < weight P.slope (product P (a+b*x) (1+v*x) (5000000+t)) := by
  let good := fun z : Gaussian => decide (0 ≤ z.1-P.slope*z.2)
  have hg (z : Gaussian) (hz : good z = true) : 0 ≤ weight P.slope (gi z) := by
    change 0 ≤ (z.1:ℝ)-(P.slope:ℝ)*(z.2:ℝ)
    exact_mod_cast (of_decide_eq_true hz : 0 ≤ z.1-P.slope*z.2)
  have hr (r : Row) (h : r.all good = true) := horner_nonneg gi P.slope good hg t ht r h
  have hp := horner_nonneg (rowVal t) P.slope (fun r => r.all good) hr x hx _ h
  change 0 ≤ weight _ (val x t (tableAdd _ _)) at hp
  rw [val_add,val_table] at hp
  have h₁ : val x t [[(-1,0)]] = -1 := by apply Complex.ext <;> simp [val,rowVal,horner,gi]
  rw [h₁] at hp
  simp [weight] at hp ⊢
  linarith

end Turan.Small34Certificate
