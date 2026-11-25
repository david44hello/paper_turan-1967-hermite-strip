-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Mathlib.Tactic

namespace Turan.Small56
namespace Certificate

-- The outer list is in increasing powers of x, the inner lists in powers of t.
def addWith {α : Type} (f : α → α → α) : List α → List α → List α
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => f a b :: addWith f p q

noncomputable def horner {α : Type} (f : α → ℝ) (x : ℝ) : List α → ℝ
  | [] => 0
  | a :: p => f a + x * horner f x p

private theorem horner_add {α : Type} (op : α → α → α) (f : α → ℝ)
    (hf : ∀ a b, f (op a b) = f a + f b) (x : ℝ) (p q : List α) :
    horner f x (addWith op p q) = horner f x p + horner f x q := by
  induction p generalizing q with
  | nil => simp [addWith, horner]
  | cons a p ih =>
    cases q <;> simp [addWith, horner, hf, ih]; ring

private theorem horner_map {α : Type} (op : α → α) (f : α → ℝ) (b x : ℝ)
    (hf : ∀ a, f (op a) = b * f a) (p : List α) :
    horner f x (p.map op) = b * horner f x p := by
  induction p with
  | nil => simp [horner]
  | cons a p ih => simp [horner, hf, ih]; ring

abbrev Row := List ℤ
abbrev Coeffs := List Row
private noncomputable abbrev ev (t : ℝ) := horner (fun n : ℤ => (n:ℝ)) t
private noncomputable abbrev val (x t : ℝ) := horner (ev t) x
private abbrev addRow := addWith (· + · : ℤ → ℤ → ℤ)
private abbrev add := addWith addRow

def linear (a b : ℤ) (p : Row) : Row :=
  addRow (p.map (a * ·)) (0 :: p.map (b * ·))

private theorem ev_add (t : ℝ) (p q : Row) : ev t (addRow p q) = ev t p + ev t q :=
  horner_add _ _ (fun _ _ => Int.cast_add ..) _ _ _

private theorem ev_linear (a b : ℤ) (p : Row) (t : ℝ) :
    ev t (linear a b p) = ((a:ℝ)+b*t)*ev t p := by
  have hs (n : ℤ) := horner_map (n * ·) (fun i : ℤ => (i:ℝ)) (n:ℝ) t
    (fun i => Int.cast_mul ..) p
  unfold linear
  rw [ev_add]
  simp only [ev, horner, Int.cast_zero, zero_add, hs]
  ring

private theorem val_add (x t : ℝ) (p q : Coeffs) :
    val x t (add p q) = val x t p + val x t q :=
  horner_add _ _ (ev_add t) _ _ _

def scale (a b : ℤ) (p : Coeffs) : Coeffs := p.map (linear a b)

private theorem val_scale (a b : ℤ) (p : Coeffs) (x t : ℝ) :
    val x t (scale a b p) = ((a:ℝ)+b*t)*val x t p :=
  horner_map _ _ _ _ (fun q => ev_linear a b q t) _

/-- Multiply by the squared distance in the chart (a+b*x)/(1+v*x),
after clearing its denominator. The ordinate squared is 860000²+t. -/
def factor (a b v c : ℤ) (p : Coeffs) : Coeffs :=
  let A := a-c
  let B := b-v*c
  add (scale (A^2+860000^2) 1 p)
    ([] :: add (scale (2*(A*B+860000^2*v)) (2*v) p)
      ([] :: scale (B^2+860000^2*v^2) (v^2) p))

def factors (a b v : ℤ) : List ℤ → Coeffs
  | [] => [[1]]
  | c :: cs => factor a b v c (factors a b v cs)

noncomputable def product (cs : List ℤ) (X V Y : ℝ) : ℝ :=
  (cs.map fun c : ℤ => (X-(c:ℝ)*V)^2+Y*V^2).prod

private theorem val_factor (a b v c : ℤ) (p : Coeffs) (x t : ℝ) :
    val x t (factor a b v c p) =
      (((a+b*x)-(c:ℝ)*(1+v*x))^2+(860000^2+t)*(1+v*x)^2)*val x t p := by
  unfold factor
  rw [val_add, val_scale]
  change _ + (0+x*val x t _) = _
  rw [val_add, val_scale]
  change _ + (0+x*(_+(0+x*val x t _))) = _
  rw [val_scale]
  push_cast
  ring

private theorem val_factors (a b v : ℤ) (cs : List ℤ) (x t : ℝ) :
    val x t (factors a b v cs) = product cs (a+b*x) (1+v*x) (860000^2+t) := by
  induction cs with
  | nil => simp [factors, val, ev, horner, product]
  | cons c cs ih => rw [factors,val_factor,ih]; simp [product]

def gamma : List ℤ := [-2048845,-2048845,2907699,2907699,2222962,2222962,2222962,
  -555650,-555650,-555650,-555650,360845]

def delta : List ℤ := [-75660,-75660,-1805569,-1805569,-626158,-626158,-626158,
  2384521,2384521,2384521,2384521,2327565]

def test (a b v : ℤ) : Bool :=
  (add [[-1]] (add (scale 81 0 (factors a b v delta)) (scale (-25) 0 (factors a b v gamma)))).all
    (fun p => p.all (0 ≤ ·))

private theorem horner_nonneg {α : Type} {f : α → ℝ} {test : α → Bool}
    (hf : ∀ a, test a = true → 0 ≤ f a) {x : ℝ} (hx : 0 ≤ x) (p : List α)
    (hp : p.all test = true) : 0 ≤ horner f x p := by
  induction p with
  | nil => simp [horner]
  | cons a p ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hp
    exact add_nonneg (hf _ hp.1) (mul_nonneg hx (ih hp.2))

theorem chart {a b v : ℤ} (h : test a b v = true) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    25*product gamma (a+b*x) (1+v*x) (860000^2+t) <
      81*product delta (a+b*x) (1+v*x) (860000^2+t) := by
  have hp := horner_nonneg (f := ev t)
    (fun p => horner_nonneg (fun (n:ℤ) hn => (by exact_mod_cast (of_decide_eq_true hn : 0 ≤ n))) ht p)
    hx _ h
  change 0 ≤ val x t (add _ _) at hp
  rw [val_add,val_add,val_scale,val_scale,val_factors,val_factors] at hp
  have hunit : val x t [[-1]] = -1 := by simp [val, ev, horner]
  rw [hunit] at hp
  norm_num at hp ⊢
  linarith only [hp]

end Certificate
end Turan.Small56
