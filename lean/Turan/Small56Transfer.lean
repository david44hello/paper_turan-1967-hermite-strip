module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.Small56Nodes
public import Turan.Small45Product

@[expose] public section

noncomputable section
namespace Turan.Small56

structure Entry where
  G : ℤ
  D : ℤ
  g : ℝ
  d : ℝ
  cert : Node G D g d
  Gsize : 2 < |(G:ℝ)|
  Dsize : 2 < |(D:ℝ)|

def distAt (w : ℂ) (s : ℝ) := ‖w-(s:ℂ)‖
def nominal (w : ℂ) (n : ℤ) := distAt w ((n:ℝ)/1000000)
def ratio (w : ℂ) (e : Entry) := distAt w e.g / distAt w e.d
def lower (e : Entry) := (|(e.G:ℝ)|-2)/(|(e.D:ℝ)|+2)
abbrev stretch : ℝ := 1 + (2/1000000)/(43/50)

theorem dist_pos (w : ℂ) (hw : 43/50 ≤ |w.im|) (s : ℝ) : 0 < distAt w s := by
  have h := Complex.abs_im_le_norm (w-(s:ℂ))
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at h
  exact (by norm_num : (0:ℝ)<43/50) |>.trans_le (hw.trans h)

theorem ratio_bound (w : ℂ) (hw : 43/50 ≤ |w.im|) (e : Entry) :
    ratio w e ≤ stretch^2 * (nominal w e.G / nominal w e.D) := by
  have hg := real_node_dist_le w e.g _ _ _ (by norm_num) hw e.cert.1
  have hd := real_node_dist_le w _ e.d _ _ (by norm_num) hw
    ((abs_sub_comm ..).trans_le e.cert.2.1)
  change distAt w e.g ≤ stretch * nominal w e.G at hg
  change nominal w e.D ≤ stretch * distAt w e.d at hd
  have h := mul_le_mul hg hd (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))
  unfold ratio
  have hp : 0 < nominal w e.D := dist_pos _ hw _
  rw [← mul_div_assoc, div_le_div_iff₀ (dist_pos w hw e.d) hp]
  linarith only [h]

private theorem abs_error {s : ℝ} {n : ℤ} (hs : |s-(n:ℝ)/1000000| ≤ 2/1000000) :
    |(n:ℝ)|-2 ≤ 1000000*|s| ∧ 1000000*|s| ≤ |(n:ℝ)|+2 := by
  have h₁ := abs_sub_abs_le_abs_sub s ((n:ℝ)/1000000)
  have h₂ := abs_sub_abs_le_abs_sub ((n:ℝ)/1000000) s
  rw [abs_sub_comm ((n:ℝ)/1000000) s] at h₂
  rw [abs_div] at h₁ h₂
  norm_num at h₁ h₂
  constructor <;> linarith only [h₁,h₂,hs]

theorem entry_d_ne (e : Entry) : e.d ≠ 0 := by
  have h := (abs_error e.cert.2.1).1
  intro he
  rw [he,abs_zero,mul_zero] at h
  linarith only [h,e.Dsize]

theorem lower_bound (e : Entry) : lower e ≤ |e.g|/|e.d| := by
  apply (div_le_div_iff₀ (by positivity) (abs_pos.mpr (entry_d_ne e))).2
  have hg := (abs_error e.cert.1).1
  have hd := (abs_error e.cert.2.1).2
  linarith only [mul_le_mul_of_nonneg_right hg (abs_nonneg e.d),
    mul_le_mul_of_nonneg_left hd (abs_nonneg e.g)]

abbrev listProd {α : Type} (s : List α) (f : α → ℝ) := (s.map f).prod

theorem listProd_nonneg {α : Type} (s : List α) (f : α → ℝ) (h : ∀ a, 0 ≤ f a) :
    0 ≤ listProd s f := List.prod_nonneg (by simpa using fun a (_ : a ∈ s) => h a)

theorem listProd_pos {α : Type} (s : List α) (f : α → ℝ) (h : ∀ a, 0 < f a) :
    0 < listProd s f := List.prod_pos (by simpa using fun a (_ : a ∈ s) => h a)

theorem list_ratio {α : Type} (s : List α) (f g : α → ℝ) :
    listProd s (fun a => f a / g a) = listProd s f / listProd s g := by
  induction s with
  | nil => simp [listProd]
  | cons a s ih => simp only [listProd,List.map_cons,List.prod_cons] at *; rw [ih]; ring

theorem list_ratio_bound (s : List Entry) (w : ℂ) (hw : 43/50 ≤ |w.im|) :
    listProd s (ratio w) ≤ (stretch^2)^s.length *
      (listProd (s.map Entry.G) (nominal w) / listProd (s.map Entry.D) (nominal w)) := by
  have hb := List.prod_map_le_prod_map₀ (s := s) (ratio w)
    (fun e => stretch^2*(nominal w e.G / nominal w e.D))
    (fun e _ => div_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun e _ => ratio_bound w hw e)
  rw [List.prod_map_mul] at hb
  simpa only [List.map_const',List.prod_replicate,list_ratio,List.map_map,Function.comp_def,
    listProd] using hb

theorem root_product (s : List Entry) (a b : ℂ)
    (hr : ∀ d : ℝ, (family 5 6 a b).eval ((d:ℂ)-1/2) ≠ 0) :
    ((family 5 6 a b).roots.map (fun z => listProd s (ratio (z+1/2)))).prod =
      listProd s (fun e => |e.g|/|e.d|) := by
  induction s with
  | nil => simp [listProd]
  | cons e s ih =>
    simp only [listProd,List.map_cons,List.prod_cons]
    rw [Multiset.prod_map_mul]
    exact congrArg₂ (· * ·) (shifted_node_product _ _ _ (e.cert.2.2 a b) (entry_d_ne e) (hr e.d)) ih

end Turan.Small56
