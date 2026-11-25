-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.NodeDefs
import Turan.IntervalAngles
import Turan.Third
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
noncomputable section
open Polynomial
namespace Turan

theorem vector_alignment_at_equal_height (U V : ℂ) (hpos : 0 < U.im) (him : U.im=V.im)
    (hcs : ‖U‖*‖V‖=U.re*V.re+U.im*V.im) : U=V := by
  have hs := congrArg (fun a : ℝ => a^2) hcs
  rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
    ← him] at hs
  have hz : ((U.re-V.re)*U.im)^2 = 0 := by linear_combination hs
  have he := (mul_eq_zero.mp ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hz)).resolve_right hpos.ne'
  exact Complex.ext (sub_eq_zero.mp he) him

theorem lower_boundary_margin (s : ℝ) :
    1/8 < h^4 ∧ 0 < 16*h^4-2 ∧
      16*h^4-2 ≤ 16*(s^2+h^2)^2+16*s^2+8*s-1 := by
  obtain ⟨_, _, _, _, hh, _⟩ := constants_spec
  have hbase : 3/4 ≤ h^2 := by nlinarith [sq_nonneg u]
  have hb : 9/16 ≤ h^4 := by nlinarith [sq_nonneg (h^2-3/4)]
  refine ⟨by linarith, by linarith, ?_⟩
  nlinarith [sq_nonneg (4*s+1), sq_nonneg (s^2), mul_nonneg (sq_nonneg s) (sq_nonneg h)]

theorem third_harmonic_and_interior (z : ℂ) (hh : h ≤ z.im) :
    InnerProductSpace.HarmonicAt (fun w : ℂ => (third w).im) z ∧
      (h < z.im → |(third z).im| < h) := by
  obtain ⟨ha, hb, he⟩ := lemma_seven.1 z hh
  refine ⟨ha.harmonicAt_im, fun hi => lt_of_le_of_ne hb ?_⟩
  intro hz
  exact hi.ne (show h = z.im by rw [he.mp hz]; rfl)

theorem family_node_form (n m : ℕ) (a b w : ℂ) (hw : w≠0) :
    (family n m a b).eval (w-1/2) = w*(2+a*nodeMode n w+b*nodeMode m w) := by
  simp [family, nodeMode, eval_add, eval_mul]
  field_simp [hw]
  <;> ring

theorem divided_powers (x y : ℂ) (hx : x≠0) (hy : y≠0) (hne : x≠y) :
    let S := x+y
    let p := x*y
    divided (fun z => z) x y=1 ∧ divided (fun z => z^2) x y=S ∧
    divided (fun z => z^3) x y=S^2-p ∧ divided (fun z => z^4) x y=S^3-2*p*S ∧
    divided (fun z => z⁻¹) x y= -1/p := by
  dsimp only
  have hxy := sub_ne_zero.mpr hne
  unfold divided
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp [hx, hy, hxy] <;> ring

theorem equal_nodes_family (n m : ℕ) (a b x y : ℂ) (hx : x≠0) (hy : y≠0) (hne : x≠y)
    (hn : divided (nodeMode n) x y=0) (hm : divided (nodeMode m) x y=0) :
    (family n m a b).eval (x-1/2)/x=(family n m a b).eval (y-1/2)/y := by
  have hxy := sub_ne_zero.mpr hne
  have he (j : ℕ) (hj : divided (nodeMode j) x y = 0) : nodeMode j x = nodeMode j y := by
    apply sub_eq_zero.mp
    exact (div_eq_zero_iff.mp hj).resolve_right hxy
  rw [family_node_form n m a b x hx, family_node_form n m a b y hy, he n hn, he m hm]
  field_simp [hx, hy]

theorem equal_nodes_ratio_and_product (n m : ℕ) (a b x y : ℂ) (hx : x≠0) (hy : y≠0) (hne : x≠y)
    (hn : divided (nodeMode n) x y=0) (hm : divided (nodeMode m) x y=0)
    (hroot : (family n m a b).eval (y-1/2) ≠ 0) :
    let F := family n m a b
    F.eval (x-1/2)/F.eval (y-1/2) = x/y ∧
    (F.roots.map (fun z => (x-(z+1/2))/(y-(z+1/2)))).prod = x/y := by
  dsimp only
  have he := (div_eq_div_iff hx hy).mp (equal_nodes_family n m a b x y hx hy hne hn hm)
  have hratio : (family n m a b).eval (x-1/2)/(family n m a b).eval (y-1/2) = x/y := (div_eq_div_iff hroot hy).mpr (by linear_combination he)
  refine ⟨hratio, ?_⟩
  let F := family n m a b
  have hp : F ≠ 0 := by intro hp; exact hroot (by change F.eval _ = 0; rw [hp]; simp)
  have hf := (IsAlgClosed.splits F).eval_eq_prod_roots
  change ((F.roots.map _).prod) = _
  rw [Multiset.prod_map_div]
  have heval (v : ℂ) : (F.roots.map (fun z => v-(z+1/2))).prod =
      (F.roots.map (fun z => (v-1/2)-z)).prod := by congr 2; funext; ring
  rw [heval x, heval y]
  change F.eval _ / F.eval _ = _ at hratio
  rwa [hf, hf, mul_div_mul_left _ _ (leadingCoeff_ne_zero.mpr hp)] at hratio

theorem equal_nodes_angle_parity (n m : ℕ) (a b : ℂ) (x y : ℝ) (hx : x≠0) (hy : y≠0)
    (hxy : x<y) (hn : divided (nodeMode n) x y=0) (hm : divided (nodeMode m) x y=0)
    (hfree : ∀ t : ℝ, (family n m a b).eval (t:ℂ) ≠ 0) :
    ∃ k : ℤ, ((family n m a b).roots.map (intervalAngle (x-1/2) (y-1/2))).sum =
      (2*(k:ℝ)+(if x*y<0 then 1 else 0))*Real.pi := by
  let F := family n m a b
  have hx' : (x:ℂ) ≠ 0 := by exact_mod_cast hx
  have hy' : (y:ℂ) ≠ 0 := by exact_mod_cast hy
  have he := equal_nodes_family n m a b x y hx' hy' (by exact_mod_cast hxy.ne) hn hm
  have hp := (div_eq_div_iff hx' hy').mp he
  have hfree' := hfree (x-1/2)
  have hval : F.eval ((y-1/2:ℝ):ℂ) / F.eval ((x-1/2:ℝ):ℂ) =
      (2*((y-1/2:ℝ):ℂ)+1)/(2*((x-1/2:ℝ):ℂ)+1) := by
    push_cast at hfree' ⊢
    apply (div_eq_div_iff hfree' (by convert mul_ne_zero (by norm_num : (2:ℂ)≠0) hx' using 1 <;> ring)).mpr
    dsimp only [F]
    linear_combination -2*hp
  obtain ⟨k, hk⟩ := equal_value_angle_sum F (x-1/2) (y-1/2) (by linarith)
    (by intro h; apply hx; linarith) (by intro h; apply hy; linarith) hfree hval
  refine ⟨k, ?_⟩
  have hs : x-1/2 < -1/2 ∧ -1/2 < y-1/2 ↔ x*y < 0 := by
    rw [mul_neg_iff]
    constructor
    · rintro ⟨hl, hr⟩
      exact Or.inr ⟨by linarith, by linarith⟩
    · rintro (⟨hl,hr⟩ | ⟨hl,hr⟩) <;> constructor <;> linarith
  simpa only [hs] using hk

end Turan
