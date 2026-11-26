module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.StripRemoveNodes
public import Turan.StripRectangle
public import Turan.StripWeightDetails
public import Turan.UpperTailStripAffine
public import Turan.UpperTailStripWeight
public import Turan.UpperTailStripMap
public import Turan.TailLines

@[expose] public section
open Set
noncomputable section
namespace Turan.StripDetails

def selected (j : ℕ) : Finset ℝ :=
  ((hermite j).roots.toFinset.filter
    (fun s => s.im=0 ∧ -(7:ℝ)/2 ≤ s.re ∧ s.re ≤ 5/2)).image Complex.re

private theorem selected_injective (j : ℕ) :
    Set.InjOn Complex.re (↑(UpperTailStrip.selectedRoots j) : Set ℂ) := by
  intro x hx y hy hxy
  exact Complex.ext hxy (((Finset.mem_filter.mp hx).2.1).trans ((Finset.mem_filter.mp hy).2.1).symm)

private theorem selected_product (j : ℕ) (z : ℂ) (hz : |z.im| ≤ height) :
    (∏ s ∈ selected j, factor s z) =
      ∏ u ∈ UpperTailStrip.selectedRoots j, TailStrip.factor u.re z := by
  classical
  change (∏ s ∈ (UpperTailStrip.selectedRoots j).image Complex.re, factor s z) = _
  rw [Finset.prod_image (selected_injective j)]
  apply Finset.prod_congr rfl
  intro u _
  exact ((UpperTailStrip.strip_tanh_image u.re).2.1 z hz).1.symm

private theorem center_product (j : ℕ) :
    ‖∏ s ∈ selected j, factor s (-1/2)‖ = nodeProduct j := by
  have hh : |(-1/2:ℂ).im| ≤ height := by norm_num [height]
  rw [selected_product j _ hh, norm_prod]
  unfold nodeProduct
  apply Finset.prod_congr rfl
  intro s _
  have hw : (-1/2:ℂ) = ((-1/2:ℝ):ℂ) := by push_cast; rfl
  rw [hw, TailStrip.factor_real, Complex.norm_real, Real.norm_eq_abs]

theorem strip_quotient_application (n m j : ℕ) (hm : 450 ≤ m) (hh : m ≤ 2*n) (hnm : n < m)
    (hj : j=n ∨ j=m) (a b : ℂ) (hs : emptyStrip (normalizedFamily n m a b) (87/100)) :
    let U := modeQuotient n m j a b
    let S := (m:ℝ)^2/((j:ℝ)*(m-n:ℝ))
    let P := fun z : ℂ => ∏ s ∈ selected j, factor s z
    ∃ V : ℂ → ℂ, (∀ z : ℂ, |z.im| < 87/100 → AnalyticAt ℂ V z) ∧
      (∀ z : ℂ, |z.im| < 87/100 → U z = V z * weight m z * P z) ∧
      (∀ z : ℂ, |z.im| = height → ‖V z‖ = ‖U z / weight m z‖) ∧
      (∀ ε > (0:ℝ), ∃ R > (0:ℝ), ∀ z : ℂ, |z.im| ≤ height → R ≤ |z.re| → ‖V z‖ < ε) ∧
      (∀ z : ℂ, |z.im| ≤ height → ‖V z‖ < 23952*S) ∧
      ‖U (-1/2)‖ ≤ 24166*S*nodeProduct j := by
  classical
  intro U S P
  have hjpos : 0 < j := by rcases hj with rfl | rfl <;> omega
  have hS : 0 < S := div_pos (by positivity) (mul_pos (by exact_mod_cast hjpos)
    (sub_pos.mpr (by exact_mod_cast hnm)))
  have hw (z : ℂ) (hz : |z.im| < 87/100) : weight m z ≠ 0 := by
    let A := Real.sqrt (2*(m:ℝ))
    have hm' : (450:ℝ) ≤ m := by exact_mod_cast hm
    have hA : 30 ≤ A := Real.le_sqrt_of_sq_le (by linarith)
    have hA₀ : (A:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    apply pow_ne_zero
    intro he
    have hv : 4*Complex.I*z = (A:ℂ) := by
      have hbase : 1 = 4*Complex.I*z/(A:ℂ) := sub_eq_zero.mp he
      simpa using (div_eq_iff hA₀).mp hbase.symm
    have hre := congrArg Complex.re hv
    norm_num [Complex.mul_re,Complex.mul_im] at hre
    linarith only [hre,hA,(abs_lt.mp hz).1]
  let f := fun z => U z / weight m z
  have ha (z : ℂ) (hz : |z.im| < 87/100) : AnalyticAt ℂ f z := by
    apply AnalyticAt.div (UpperTailStrip.quotient_analytic n m j a b z hz (hs z hz)) _ (hw z hz)
    unfold weight
    fun_prop
  have hzero (s : ℝ) (hs' : s ∈ selected j) : f (s:ℂ)=0 := by
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hs'
    obtain ⟨hur,hreal,_⟩ := Finset.mem_filter.mp hu
    have he : (hermite j).eval u = 0 := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hur)
    have hu' : (u.re : ℂ) = u := Complex.ext rfl hreal.symm
    simp [f,U,modeQuotient,psi,hu',he]
  obtain ⟨V,hV,hfac,hline⟩ := strip_remove_nodes (selected j) f ha hzero
  have hfull (z : ℂ) (hz : |z.im| < 87/100) : U z = V z * weight m z * P z := by
    have he : U z / weight m z = V z * P z := hfac z hz
    rw [div_eq_iff (hw z hz)] at he
    rw [he]
    ring
  have hnarrow (z : ℂ) (hz : |z.im| ≤ height) : |z.im| < 87/100 :=
    hz.trans_lt (by norm_num [height])
  have hfar : ∀ ε > (0:ℝ), ∃ R > (0:ℝ), ∀ z : ℂ, |z.im| ≤ height → R ≤ |z.re| → ‖V z‖ < ε := by
    intro ε hε
    obtain ⟨R,hR,hdecay⟩ := UpperTailStrip.weighted_decay n m j hm hh hnm hj a b ε hε
    refine ⟨max R 4, lt_of_lt_of_le hR (le_max_left ..), ?_⟩
    intro z hz hzR
    have hn := hnarrow z hz
    have hp : P z ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro s hs'
      obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hs'
      obtain ⟨_,_,hlo,hhi⟩ := Finset.mem_filter.mp hu
      intro hp
      have hsEq := ((strip_factor_divisor s).2.2.1 z hn).2.mp hp
      have hre : z.re = s := congrArg Complex.re hsEq
      have hhabs : |z.re| < 4 := abs_lt.mpr ⟨by linarith,by linarith⟩
      exact hhabs.not_ge ((le_max_right R 4).trans hzR)
    have hd := (hdecay z hz ((le_max_left R 4).trans hzR)).2
    change ‖U z / (weight m z * ∏ u ∈ UpperTailStrip.selectedRoots j, TailStrip.factor u.re z)‖ < ε at hd
    rw [← selected_product j z hz] at hd
    change ‖U z / (weight m z * P z)‖ < ε at hd
    rwa [hfull z hn,mul_assoc,mul_div_cancel_right₀ _ (mul_ne_zero (hw z hn) hp)] at hd
  have hVbd (z : ℂ) (hy : |z.im| = height) : ‖V z‖ < 23952*S := by
    rw [hline z hy]
    have hb := boundary_weighted_quotient m j n hm hjpos hnm z (U z) hy
      (lemma_fifteen n m hm hh hnm a b hs j hj z hy)
    exact hb.1.trans_lt hb.2
  have hmax := (strip_rectangle_maximum V (23952*S) (by positivity)
    (fun z hz => hV z (hnarrow z hz)) hVbd (fun ε he => by
      obtain ⟨R,_,hR⟩ := hfar ε he
      exact ⟨R,hR⟩)).2
  refine ⟨V,hV,hfull,hline,hfar,hmax,?_⟩
  let w : ℂ := -1/2
  have hwy : |w.im| ≤ height := by norm_num [w,height]
  have hp : ‖P w‖ = nodeProduct j := center_product j
  have hprod : 0 ≤ nodeProduct j := hp ▸ norm_nonneg _
  obtain ⟨he,hl,hmul,_⟩ := strip_center_weight m hm
  change ‖U w‖ ≤ _
  rw [hfull w (hnarrow w hwy),norm_mul,norm_mul,hp]
  apply mul_le_mul_of_nonneg_right _ hprod
  calc
    _ ≤ (23952*S) * (226/225)^2 := mul_le_mul (hmax w hwy).le (he.le.trans hl)
      (norm_nonneg _) (by positivity)
    _ = (23952*(226/225:ℝ)^2)*S := by ring
    _ ≤ 24166*S := mul_le_mul_of_nonneg_right hmul.le hS.le

#print axioms strip_quotient_application

end Turan.StripDetails
