-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Defs
import Turan.Small45Sextic
import Turan.Small45Product
import Mathlib.Analysis.Complex.AbsMax

noncomputable section

open scoped Topology
open Filter Set Metric
namespace Turan.Small45

/-- The two symmetric divided-difference formulas of A.3, in the independent
sum and product variables. At distinct nonzero arguments they are [q₄], [q₅]. -/
theorem divided_differences_zero_iff_eliminant (S p : ℂ) (hS : S ≠ -9) (hp : p ≠ 0) :
    (16 * (S^2 - p) - 32*S - 24 - 1/p = 0 ∧
      32 * (S^3 - 2*p*S) - 80 * (S^2 - p) - 80*S + 200 + 41/p = 0) ↔
    p = (2*S^3 + 36*S^2 - 87*S - 49) / (4*S + 36) ∧
      S^6 + 14*S^5 - 111*S^4 + 228*S^3 - 143*S^2 - 6*S + 41 = 0 := by
  let d := 4*S + 36
  let n := 2*S^3 + 36*S^2 - 87*S - 49
  let e := S^6 + 14*S^5 - 111*S^4 + 228*S^3 - 143*S^2 - 6*S + 41
  let a := (16*(S^2-p) - 32*S - 24)*p - 1
  let b := (32*(S^3-2*p*S) - 80*(S^2-p) - 80*S + 200)*p + 41
  have hd : d ≠ 0 := by
    intro h
    apply hS
    linear_combination (norm := (dsimp [d]; ring)) h / 4
  -- The linear combination eliminates the reciprocal and isolates d*p - n.
  have hab : b + 41*a = -16*p*(d*p-n) := by dsimp [a,b,d,n]; ring
  have he : d^2*a = 64*e +
      ((16*S^2-32*S-24)*d-16*(d*p+n))*(d*p-n) := by dsimp [d,a,e,n]; ring
  have ha : 16*(S^2-p)-32*S-24-1/p = 0 ↔ a = 0 := by
    dsimp [a]
    constructor <;> intro h
    · field_simp [hp] at h
      linear_combination h
    · field_simp [hp]
      linear_combination h
  have hb : 32*(S^3-2*p*S)-80*(S^2-p)-80*S+200+41/p = 0 ↔ b = 0 := by
    dsimp [b]
    constructor <;> intro h
    · field_simp [hp] at h
      linear_combination h
    · field_simp [hp]
      linear_combination h
  rw [ha,hb]
  change (a = 0 ∧ b = 0) ↔ p = n/d ∧ e = 0
  rw [eq_div_iff hd, mul_comm p d, ← sub_eq_zero (a := d*p) (b := n)]
  constructor
  · rintro ⟨ha₀,hb₀⟩
    rw [ha₀,hb₀] at hab
    have ht : d*p-n = 0 := (mul_eq_zero.mp (by simpa using hab.symm)).resolve_left
      (mul_ne_zero (by norm_num : (-16:ℂ) ≠ 0) hp)
    refine ⟨ht, ?_⟩
    rw [ha₀,ht] at he
    linear_combination -he / 64
  · rintro ⟨ht,he₀⟩
    rw [ht,he₀] at he
    have ha₀ : a = 0 := (mul_eq_zero.mp (by simpa using he)).resolve_left (pow_ne_zero 2 hd)
    exact ⟨ha₀, by simpa [ha₀,ht] using hab⟩

/-- The shifted-coordinate rational function, with its first pair counted twice. -/
def nodeQuotient (l r u v : ℝ) (w : ℂ) : ℂ :=
  (w - l)^2 * (w - u) / ((w - r)^2 * (w - v))

def modelQuotient : ℂ → ℂ := nodeQuotient (-20.10) 0 0.44 2.47

private def numerator (z : ℂ) : ℂ := (z + 20.10)^2 * (z - 0.44)
private def denominator (z : ℂ) : ℂ := z^2 * (z - 2.47)

private lemma model_eq (z : ℂ) : modelQuotient z = numerator z / denominator z := by
  simp [modelQuotient,nodeQuotient,numerator,denominator,sub_neg_eq_add]

private lemma analytic_model {w : ℂ} (h₀ : w ≠ 0) (h₁ : w ≠ 2.47) :
    AnalyticAt ℂ modelQuotient w := by
  rw [show modelQuotient = fun z => numerator z / denominator z from funext model_eq]
  apply AnalyticAt.div
  · unfold numerator
    fun_prop
  · unfold denominator
    fun_prop
  · exact mul_ne_zero (pow_ne_zero 2 h₀) (sub_ne_zero.mpr h₁)

private theorem model_infinity : Tendsto modelQuotient (cocompact ℂ) (𝓝 1) := by
  let g (t : ℂ) := (1+20.10*t)^2*(1-0.44*t)/(1-2.47*t)
  have hc : ContinuousAt g 0 := by unfold g; fun_prop (disch := norm_num)
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hg : Tendsto (fun z : ℂ => g z⁻¹) (cocompact ℂ) (𝓝 1) := by
    simpa only [Function.comp_def, show g 0 = 1 by simp [g]] using hc.tendsto.comp hi
  apply hg.congr'
  filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with z hz
  have hn : z ≠ 0 := hz
  rw [model_eq]
  dsimp [g,numerator,denominator]
  rw [← mul_div_mul_right _ _ (pow_ne_zero 3 hn)]
  congr 1 <;> field_simp [hn]

private lemma pole_limit (w : ℂ) (hw : w = 0 ∨ w = 2.47) :
    Tendsto (fun z => ‖modelQuotient z‖) (𝓝[≠] w) atTop := by
  have hD : denominator w = 0 := by rcases hw with rfl | rfl <;> simp [denominator]
  have hN : 0 < ‖numerator w‖ := by
    apply norm_pos_iff.mpr
    rcases hw with rfl | rfl <;> norm_num [numerator]
  have avoid (a : ℂ) : ∀ᶠ z in 𝓝[≠] w, z ≠ a := by
    rcases eq_or_ne w a with rfl | h
    · exact self_mem_nhdsWithin
    · exact eventually_ne_nhdsWithin h
  have hd : Tendsto denominator (𝓝[≠] w) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · rw [← hD]
      exact (show Continuous denominator by unfold denominator; fun_prop).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    · filter_upwards [avoid 0, avoid 2.47] with z h₀ h₁
      exact mul_ne_zero (pow_ne_zero 2 h₀) (sub_ne_zero.mpr h₁)
  have hn : Tendsto (fun z => ‖numerator z‖) (𝓝[≠] w) (𝓝 ‖numerator w‖) :=
    (show Continuous numerator by unfold numerator; fun_prop).norm.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  simpa only [model_eq,div_eq_mul_inv,norm_mul,Function.comp_def] using
    hn.pos_mul_atTop hN (tendsto_norm_inv_nhdsNE_zero_atTop.comp hd)
/-- Finite poles are characterized by blowup on a punctured neighbourhood. -/
theorem model_poles_and_infinity :
    (∀ w : ℂ, (Filter.Tendsto (fun z => ‖modelQuotient z‖) (𝓝[≠] w) Filter.atTop ↔
      w = 0 ∨ w = 2.47)) ∧
    (∀ w : ℂ, w ≠ 0 → w ≠ 2.47 → AnalyticAt ℂ modelQuotient w) ∧
    Filter.Tendsto modelQuotient (Filter.cocompact ℂ) (𝓝 1) := by
  refine ⟨fun w => ⟨?_, pole_limit w⟩, fun _ => analytic_model, model_infinity⟩
  intro h
  by_contra! hn
  exact not_tendsto_atTop_of_tendsto_nhds
    ((analytic_model hn.1 hn.2).continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds) h

private lemma dist_real_pos (w : ℂ) (hw : 17/20 ≤ |w.im|) (s : ℝ) :
    0 < ‖w-(s:ℂ)‖ :=
  lt_of_lt_of_le (by norm_num : (0:ℝ) < 17/20)
    (hw.trans (by simpa using Complex.abs_im_le_norm (w-(s:ℂ))))

private lemma model_product_lt (w : ℂ) (hw : 17/20 ≤ |w.im|) :
    ‖w-((-20.10:ℝ):ℂ)‖^2 * ‖w-((0.44:ℝ):ℂ)‖ <
      225 * ‖w-((0:ℝ):ℂ)‖^2 * ‖w-((2.47:ℝ):ℂ)‖ := by
  have hs (s : ℝ) : ‖w-(s:ℂ)‖^2 = (w.re-s)^2+w.im^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply,pow_two]
  apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow,hs,sub_neg_eq_add,sub_zero]
  exact model_sextic _ _ hw

private lemma model_strict (w : ℂ) (hw : 17/20 ≤ |w.im|) : ‖modelQuotient w‖ < 225 := by
  simp only [modelQuotient,nodeQuotient,norm_div,norm_mul,norm_pow]
  apply (div_lt_iff₀ (mul_pos (pow_pos (dist_real_pos w hw 0) 2) (dist_real_pos w hw 2.47))).mpr
  simpa only [mul_assoc] using model_product_lt w hw

private lemma far_bound (c : ℂ) (B : ℝ) (hB : 1 < B) :
    ∃ R > (0 : ℝ), ∀ z : ℂ, R ≤ ‖z-c‖ → ‖modelQuotient z‖ ≤ B := by
  have ht : Tendsto (fun z => ‖modelQuotient z‖) (cocompact ℂ) (𝓝 1) := by
    simpa only [norm_one] using model_infinity.norm
  obtain ⟨r,hr⟩ := (mem_cocompact_iff_closedBall_compl_subset c).mp (ht.eventually_lt_const hB)
  refine ⟨max 0 r + 1, by positivity, fun z hz => le_of_lt (hr ?_)⟩
  change ¬ dist z c ≤ r
  rw [dist_eq_norm]
  linarith [le_max_right (0:ℝ) r]

private lemma analytic_above (w : ℂ) (hw : 17/20 ≤ w.im) : AnalyticAt ℂ modelQuotient w := by
  apply analytic_model <;> intro he <;> rw [he] at hw <;> norm_num at hw

theorem model_boundary_margin :
    ∃ B ∈ Set.Ioo (1 : ℝ) 225, ∀ w : ℂ, w.im = 17/20 → ‖modelQuotient w‖ ≤ B := by
  let c : ℂ := ⟨0,17/20⟩
  obtain ⟨R,hR,hfar⟩ := far_bound c 2 (by norm_num)
  let K := closedBall c R ∩ {z : ℂ | z.im = 17/20}
  have hK : IsCompact K :=
    (isCompact_closedBall c R).inter_right (isClosed_eq Complex.continuous_im continuous_const)
  have hc : c ∈ K := ⟨mem_closedBall_self hR.le, rfl⟩
  have hcont : ContinuousOn (fun z => ‖modelQuotient z‖) K := fun z hz =>
    (analytic_above z (le_of_eq hz.2.symm)).continuousAt.norm.continuousWithinAt
  -- Outside the ball the norm is at most 2. Inside, the line maximum is attained.
  obtain ⟨z,hz,hmax⟩ := hK.exists_isMaxOn ⟨c,hc⟩ hcont
  have him : z.im = 17/20 := hz.2
  have hlt := model_strict z (by rw [him]; norm_num)
  refine ⟨max 2 ‖modelQuotient z‖, ⟨lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) (le_max_left ..),
    max_lt (by norm_num) hlt⟩, ?_⟩
  intro w hw
  by_cases h : w ∈ closedBall c R
  · exact (isMaxOn_iff.mp hmax w ⟨h,hw⟩).trans (le_max_right ..)
  · have hout : R < ‖w-c‖ := by simpa [mem_closedBall,dist_eq_norm] using h
    exact (hfar w hout.le).trans (le_max_left ..)

/-- A uniform diameter bound above the limit at infinity controls the large
semicircles and their filled half-disks. Reflection gives the same cap below. -/
theorem model_half_disk_extension (B : ℝ) (hB : 1 < B)
    (hline : ∀ w : ℂ, w.im = 17/20 → ‖modelQuotient w‖ ≤ B) :
    let c : ℂ := (17/20) * Complex.I
    (∃ R₀ > (0 : ℝ), ∀ R ≥ R₀,
      (∀ w : ℂ, 17/20 ≤ w.im → ‖w-c‖ = R → ‖modelQuotient w‖ ≤ B) ∧
      (∀ w : ℂ, 17/20 ≤ w.im → ‖w-c‖ ≤ R → ‖modelQuotient w‖ ≤ B)) ∧
    (∀ w : ℂ, modelQuotient (star w) = star (modelQuotient w)) ∧
    (∀ w : ℂ, 17/20 ≤ |w.im| → ‖modelQuotient w‖ ≤ B) := by
  dsimp only
  let c : ℂ := (17/20) * Complex.I
  obtain ⟨r,hr,hfar⟩ := far_bound c B hB
  let H := Complex.im ⁻¹' Ici (17/20 : ℝ)
  have hH : IsClosed H := isClosed_Ici.preimage Complex.continuous_im
  have disk (R : ℝ) (hR : r ≤ R) (w : ℂ) (hw : 17/20 ≤ w.im) (hd : ‖w-c‖ ≤ R) :
      ‖modelQuotient w‖ ≤ B := by
    let K := closedBall c R ∩ H
    have hK : IsClosed K := isClosed_closedBall.inter hH
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      (U := K) (isBounded_closedBall.subset inter_subset_left)
    · apply hK.diffContOnCl_iff.mpr
      intro z hz
      exact (analytic_above z hz.2).differentiableAt.differentiableWithinAt
    · intro z hz
      -- Each frontier point lies on the circular arc or on the diameter.
      rcases frontier_inter_subset (closedBall c R) H hz with ha | hb
      · have hs : ‖z-c‖ = R := by
          simpa only [mem_sphere,dist_eq_norm] using frontier_closedBall_subset_sphere ha.1
        exact hfar z (hR.trans hs.ge)
      · have hl := Complex.continuous_im.frontier_preimage_subset (Ici (17/20 : ℝ)) hb.2
        exact hline z (by simpa [frontier_Ici] using hl)
    · rw [hK.closure_eq]
      exact ⟨(mem_closedBall.mpr (by simpa [dist_eq_norm] using hd)),hw⟩
  have refl (w : ℂ) : modelQuotient (star w) = star (modelQuotient w) := by
    simp only [modelQuotient, nodeQuotient, Complex.star_def, map_div₀, map_mul, map_pow,
      map_sub, Complex.conj_ofReal]
  refine ⟨⟨r, hr, fun R hR => ⟨fun w _ hw => hfar w (hR.trans hw.ge),disk R hR⟩⟩,refl,?_⟩
  intro w hw
  have upper (z : ℂ) (hz : 17/20 ≤ z.im) :=
    disk (max r ‖z-c‖) (le_max_left ..) z hz (le_max_right ..)
  rcases le_abs.mp hw with h | h
  · exact upper w h
  · have hh := upper (star w) (by simpa [Complex.star_def] using h)
    simpa only [refl,norm_star] using hh

theorem node_quotient_strict_transfer (l r u v : ℝ)
    (hl : l ∈ Set.Ioo (-20.11) (-20.09)) (hr : r ∈ Set.Ioo (-1/125000) 0)
    (hu : u ∈ Set.Ioo 0.43 0.45) (hv : v ∈ Set.Ioo 2.46 2.48)
    (w : ℂ) (hw : 17/20 ≤ |w.im|) :
    ‖nodeQuotient l r u v w‖ < 225 * (86/85)^4 * (1 + 1/106250)^2 := by
  let d (s : ℝ) := ‖w-(s:ℂ)‖
  let k : ℝ := 86/85
  let j : ℝ := 1+1/106250
  have hd (s : ℝ) : 0 < d s := dist_real_pos w hw s
  have hk : 0 < k := by norm_num [k]
  have close (s t : ℝ) (h : |s-t| ≤ 0.01) : d s ≤ k*d t := by
    convert real_node_dist_le w s t 0.01 (17/20) (by norm_num) hw h using 1
    norm_num [d,k]
  have hL := close l (-20.10) (abs_le.mpr ⟨by linarith [hl.1],by linarith [hl.2]⟩)
  have hU := close u 0.44 (abs_le.mpr ⟨by linarith [hu.1],by linarith [hu.2]⟩)
  have hV := close 2.47 v (abs_le.mpr ⟨by linarith [hv.2],by linarith [hv.1]⟩)
  have hR : d 0 ≤ j*d r := by
    convert real_node_dist_le w 0 r (1/125000) (17/20) (by norm_num) hw
      (abs_le.mpr ⟨by linarith [hr.2],by linarith [hr.1]⟩) using 1
    norm_num [d,j]
  simp only [nodeQuotient,norm_div,norm_mul,norm_pow]
  change (d l^2*d u)/(d r^2*d v) < 225*k^4*j^2
  apply (div_lt_iff₀ (mul_pos (pow_pos (hd r) 2) (hd v))).mpr
  calc
    d l^2*d u ≤ (k*d (-20.10))^2*(k*d 0.44) := by gcongr
    _ = k^3*(d (-20.10)^2*d 0.44) := by ring
    _ < k^3*(225*d 0^2*d 2.47) := mul_lt_mul_of_pos_left (model_product_lt w hw) (pow_pos hk 3)
    _ ≤ k^3*(225*(j*d r)^2*(k*d v)) := by gcongr
    _ = (225*k^4*j^2)*(d r^2*d v) := by ring

#print axioms divided_differences_zero_iff_eliminant
#print axioms model_poles_and_infinity
#print axioms model_boundary_margin
#print axioms model_half_disk_extension
#print axioms node_quotient_strict_transfer

end Turan.Small45
