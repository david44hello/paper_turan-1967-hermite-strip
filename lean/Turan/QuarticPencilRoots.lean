module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.QuarticPencilDefs
public import Turan.QuarticStability

@[expose] public section

noncomputable section
open Polynomial Filter Set Metric
open scoped Topology
namespace Turan

private abbrev largeD := comap (fun d : ℝ => |d|) atTop

private theorem inv_largeD : Tendsto (fun d : ℝ => d⁻¹) largeD (𝓝 0) := by
  simpa only [largeD, ← Real.norm_eq_abs, comap_norm_atTop] using
    (Filter.tendsto_inv₀_cobounded (α := ℝ))

private theorem contact_degree_four (d : ℝ) : (contactPencilPoly d).natDegree = 4 := by
  unfold contactPencilPoly
  compute_degree!

/-- In the fixed coordinate, u squared times the pencil extends polynomially to u = 0. -/
private def finiteModel (u : ℝ) : Polynomial ℂ :=
  (2*C (u:ℂ)*X+1)^2*(4*X^2+4*X+2) - C (u:ℂ)^2*(4*X^4-4*X^2+3)

private theorem finiteModel_eval (u : ℝ) (z : ℂ) :
    (finiteModel u).eval z =
      (2*(u:ℂ)*z+1)^2*(4*z^2+4*z+2) - (u:ℂ)^2*(4*z^4-4*z^2+3) := by
  simp [finiteModel, eval_sub, eval_add, eval_pow, eval_mul]

private theorem finite_witness (c : ℂ) (hc : 4*c^2+4*c+2=0)
    (r : ℝ) (hr : 0 < r) :
    ∀ᶠ d in largeD, ∃ z ∈ (contactPencilPoly d).roots, ‖z-c‖ < r := by
  have hcont : Continuous (fun v : ℝ × ℂ => (finiteModel v.1).eval v.2) := by
    simp only [finiteModel_eval]
    fun_prop
  have hne : finiteModel 0 ≠ 0 := by
    intro h
    have := congrArg (eval (0 : ℂ)) h
    norm_num [finiteModel_eval] at this
  have hc' : (finiteModel 0).eval c = 0 := by simp [finiteModel_eval, hc]
  have hroot := inv_largeD.eventually (nearby_polynomial_root finiteModel hcont 0 hne c hc' r hr)
  filter_upwards [hroot, tendsto_comap.eventually (eventually_gt_atTop (0 : ℝ))] with d hd hpos
  have hd' : d ≠ 0 := abs_pos.mp hpos
  have hdc : (d:ℂ) ≠ 0 := by exact_mod_cast hd'
  obtain ⟨z,hz,hdist⟩ := hd
  have hp : contactPencilPoly d ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (contactPencilPoly d).natDegree by rw [contact_degree_four]; decide)
  refine ⟨z, (mem_roots hp).mpr ?_, by simpa only [dist_eq_norm] using hdist⟩
  change (contactPencilPoly d).eval z = 0
  rw [finiteModel_eval, Complex.ofReal_inv] at hz
  rw [contactPencilPoly_eval]
  field_simp [hdc] at hz
  linear_combination hz

/-- Value at t of the rescaled real pencil, in the reciprocal parameter u. -/
private def realModel (u t : ℝ) : ℝ :=
  (2*t+1)^2*(4*t^2+4*u*t+2*u^2) - (4*t^4-4*u^2*t^2+3*u^4)

private theorem realModel_zero (t : ℝ) :
    realModel 0 t = 4*t^2*(3*t+1)*(t+1) := by unfold realModel; ring

private theorem sign_interval (l h : ℝ) (hlh : l ≤ h)
    (hs : (0 < realModel 0 l ∧ realModel 0 h < 0) ∨
          (realModel 0 l < 0 ∧ 0 < realModel 0 h)) :
    ∀ᶠ u in 𝓝 (0:ℝ), ∃ t ∈ Icc l h, realModel u t = 0 := by
  have hc (x : ℝ) : ContinuousAt (fun u => realModel u x) 0 := by unfold realModel; fun_prop
  have ht (u : ℝ) : ContinuousOn (realModel u) (Icc l h) := by unfold realModel; fun_prop
  rcases hs with ⟨hl,hh⟩ | ⟨hl,hh⟩
  · filter_upwards [(hc l).tendsto.eventually (eventually_gt_nhds hl),
      (hc h).tendsto.eventually (eventually_lt_nhds hh)] with u hu hv
    exact intermediate_value_Icc' hlh (ht u) ⟨hv.le, hu.le⟩
  · filter_upwards [(hc l).tendsto.eventually (eventually_lt_nhds hl),
      (hc h).tendsto.eventually (eventually_gt_nhds hh)] with u hu hv
    exact intermediate_value_Icc hlh (ht u) ⟨hu.le, hv.le⟩

private theorem real_intervals (r : ℝ) (hr : 0 < r) (hr' : r < 1/6) :
    ∀ᶠ u in 𝓝 (0:ℝ), (∃ t : ℝ, |t+1| < r ∧ realModel u t = 0) ∧
      (∃ t : ℝ, |t+1/3| < r ∧ realModel u t = 0) := by
  have weight {t : ℝ} (ht : t < 0) : 0 < 4*t^2 :=
    mul_pos (by norm_num) (sq_pos_of_ne_zero ht.ne)
  have atOne := sign_interval (-1-r/2) (-1+r/2) (by linarith) (Or.inl (by
    rw [realModel_zero, realModel_zero]
    constructor
    · exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (weight (by linarith)) (by linarith)) (by linarith)
    · exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (weight (by linarith)) (by linarith)) (by linarith)))
  have atThird := sign_interval (-1/3-r/2) (-1/3+r/2) (by linarith) (Or.inr (by
    rw [realModel_zero, realModel_zero]
    constructor
    · exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (weight (by linarith)) (by linarith)) (by linarith)
    · exact mul_pos (mul_pos (weight (by linarith)) (by linarith)) (by linarith)))
  filter_upwards [atOne, atThird] with u h₁ h₂
  obtain ⟨s,⟨hsl,hsr⟩,hs⟩ := h₁
  obtain ⟨t,⟨htl,htr⟩,ht⟩ := h₂
  exact ⟨⟨s, abs_lt.mpr ⟨by linarith, by linarith⟩, hs⟩,
         ⟨t, abs_lt.mpr ⟨by linarith, by linarith⟩, ht⟩⟩

private theorem scaled_root (d t : ℝ) (hd : d ≠ 0) (ht : realModel d⁻¹ t = 0) :
    ((d*t : ℝ) : ℂ) ∈ (contactPencilPoly d).roots := by
  have hp : contactPencilPoly d ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (contactPencilPoly d).natDegree by rw [contact_degree_four]; decide)
  apply (mem_roots hp).mpr
  change (contactPencilPoly d).eval _ = 0
  rw [contactPencilPoly_eval]
  unfold realModel at ht
  field_simp [hd] at ht
  exact_mod_cast (show (2*(d*t)+d)^2*(4*(d*t)^2+4*(d*t)+2) -
    (4*(d*t)^4-4*(d*t)^2+3) = 0 by linear_combination ht)

private def upperCenter : ℂ := -1/2+Complex.I/2
private def lowerCenter : ℂ := -1/2-Complex.I/2

private theorem fixed_bounds {c z : ℂ} {r : ℝ} (hc : c.re = -1/2)
    (hr : r < 1/6) (hz : ‖z-c‖ < r) :
    |z.re| < 1 ∧ c.im-r < z.im ∧ z.im < c.im+r := by
  obtain ⟨h₁,h₂⟩ := abs_lt.mp ((Complex.abs_re_le_norm (z-c)).trans_lt hz)
  obtain ⟨h₃,h₄⟩ := abs_lt.mp ((Complex.abs_im_le_norm (z-c)).trans_lt hz)
  rw [Complex.sub_re, hc] at h₁ h₂
  rw [Complex.sub_im] at h₃ h₄
  exact ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

private def scaledDisk (d x r : ℝ) (z : ℂ) : Prop :=
  ‖z/(d:ℂ)+(x:ℂ)‖ < r

private theorem scaled_re {d x r : ℝ} {z : ℂ} (h : scaledDisk d x r z) :
    |z.re/d+x| < r := by
  simpa only [Complex.add_re, Complex.div_ofReal_re, Complex.ofReal_re] using
    (Complex.abs_re_le_norm (z/(d:ℂ)+(x:ℂ))).trans_lt h

private theorem fixed_excludes_scaled {d x r : ℝ} {z : ℂ} (hd : 12 ≤ |d|)
    (hx : 1/3 ≤ x) (hr : r < 1/6) (hz : |z.re| < 1) : ¬ scaledDisk d x r z := by
  intro h
  have hsmall : |z.re/d| < 1/6 := by
    rw [abs_div, div_lt_iff₀ (by linarith : 0 < |d|)]
    linarith
  linarith [(abs_lt.mp hsmall).1, (abs_lt.mp (scaled_re h)).2]

private theorem scaled_real {d t x r : ℝ} (hd : d ≠ 0) (ht : |t+x| < r) :
    scaledDisk d x r ((d*t : ℝ):ℂ) := by
  have hdc : (d:ℂ) ≠ 0 := by exact_mod_cast hd
  simpa [scaledDisk, Complex.ofReal_mul, mul_div_cancel_left₀ _ hdc,
    ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs] using ht

/-- Four distinct witnesses exhaust a root multiset of cardinality at most four. -/
private theorem four_cells {α : Type*} (s : Multiset α) (A B G H R : α → Prop)
    [DecidablePred A] [DecidablePred B] [DecidablePred G] [DecidablePred H]
    (a b c e : α) (hs : s.card ≤ 4)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (he : e ∈ s)
    (ha' : A a ∧ ¬B a ∧ ¬G a ∧ ¬H a) (hb' : ¬A b ∧ B b ∧ ¬G b ∧ ¬H b)
    (hc' : ¬A c ∧ ¬B c ∧ G c ∧ ¬H c ∧ R c) (he' : ¬A e ∧ ¬B e ∧ ¬G e ∧ H e ∧ R e) :
    (s.filter A).card=1 ∧ (s.filter B).card=1 ∧ (s.filter G).card=1 ∧
    (s.filter H).card=1 ∧ (∀ z ∈ s, A z ∨ B z ∨ G z ∨ H z) ∧
    (∀ z ∈ s, G z ∨ H z → R z) := by
  classical
  obtain ⟨aa,ab,ag,ah⟩ := ha'
  obtain ⟨ba,bb,bg,bh⟩ := hb'
  obtain ⟨ca,cb,cg,ch,cr⟩ := hc'
  obtain ⟨ea,eb,eg,eh,er⟩ := he'
  let v := a ::ₘ b ::ₘ c ::ₘ e ::ₘ (0 : Multiset α)
  have hn : v.Nodup := by
    simp [v, Multiset.nodup_cons]
    grind
  have hv : v ≤ s := (Multiset.le_iff_subset hn).mpr (by
    intro z hz
    simp only [v, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption)
  rw [← Multiset.eq_of_le_of_card_le hv (by simpa [v] using hs)]
  simp [v, Multiset.filter_singleton, aa,ab,ag,ah,ba,bb,bg,bh,
    ca,cb,cg,ch,cr,ea,eb,eg,eh,er]

/-- The fixed disks contain the two bounded roots. The rescaled disks each contain
one real root. These four distinct witnesses exhaust the degree with multiplicity. -/
theorem quartic_pencil_large_parameter_roots (r : ℝ) (hr₀ : 0<r) (hr₁ : r<1/6) :
    ∀ᶠ d : ℝ in comap (fun u : ℝ => |u|) atTop,
      let roots := (contactPencilPoly d).roots
      let nearUpper := fun z : ℂ => ‖z-(-1/2+Complex.I/2)‖ < r
      let nearLower := fun z : ℂ => ‖z-(-1/2-Complex.I/2)‖ < r
      let g₁ := fun z : ℂ => ‖z/(d:ℂ)+1‖ < r
      let g₂ := fun z : ℂ => ‖z/(d:ℂ)+1/3‖ < r
      (roots.filter nearUpper).card=1 ∧ (roots.filter nearLower).card=1 ∧
      (roots.filter g₁).card=1 ∧ (roots.filter g₂).card=1 ∧
      (∀ z ∈ roots, nearUpper z ∨ nearLower z ∨ g₁ z ∨ g₂ z) ∧
      (∀ z ∈ roots, g₁ z ∨ g₂ z → z.im=0) := by
  classical
  have up := finite_witness upperCenter (by unfold upperCenter; linear_combination Complex.I_sq) r hr₀
  have lo := finite_witness lowerCenter (by unfold lowerCenter; linear_combination Complex.I_sq) r hr₀
  filter_upwards [up, lo, inv_largeD.eventually (real_intervals r hr₀ hr₁),
    tendsto_comap.eventually (eventually_ge_atTop (12 : ℝ))] with d hu hl hreal hd
  change 12 ≤ |d| at hd
  have hd₀ : d ≠ 0 := abs_pos.mp (by linarith)
  obtain ⟨a,ha,haU⟩ := hu
  obtain ⟨b,hb,hbL⟩ := hl
  obtain ⟨⟨s,hs,hsroot⟩,⟨t,ht,htroot⟩⟩ := hreal
  let A := fun z : ℂ => ‖z-upperCenter‖ < r
  let B := fun z : ℂ => ‖z-lowerCenter‖ < r
  have upper {z : ℂ} (hz : A z) : |z.re| < 1 ∧ 0 < z.im := by
    have h := fixed_bounds (c := upperCenter) (by norm_num [upperCenter, Complex.add_re,
      Complex.div_ofNat_re]) hr₁ hz
    have hi : upperCenter.im = 1/2 := by norm_num [upperCenter, Complex.add_im, Complex.div_ofNat_im]
    exact ⟨h.1, by linarith [h.2.1]⟩
  have lower {z : ℂ} (hz : B z) : |z.re| < 1 ∧ z.im < 0 := by
    have h := fixed_bounds (c := lowerCenter) (by norm_num [lowerCenter, Complex.sub_re,
      Complex.div_ofNat_re]) hr₁ hz
    have hi : lowerCenter.im = -1/2 := by norm_num [lowerCenter, Complex.sub_im, Complex.div_ofNat_im]
    exact ⟨h.1, by linarith [h.2.2]⟩
  have hG := scaled_real hd₀ hs
  have hH := scaled_real hd₀ ht
  have sep {z : ℂ} (h : scaledDisk d 1 r z) : ¬ scaledDisk d (1/3) r z := by
    intro h'
    linarith [(abs_lt.mp (scaled_re h)).2, (abs_lt.mp (scaled_re h')).1]
  have notUpper (x : ℝ) : ¬ A (x:ℂ) := fun h => (lt_irrefl 0) (upper h).2
  have notLower (x : ℝ) : ¬ B (x:ℂ) := fun h => (lt_irrefl 0) (lower h).2
  have four := four_cells (contactPencilPoly d).roots A B (scaledDisk d 1 r)
    (scaledDisk d (1/3) r) (fun z : ℂ => z.im=0) a b ((d*s:ℝ):ℂ) ((d*t:ℝ):ℂ)
    ((contactPencilPoly d).card_roots'.trans_eq (contact_degree_four d))
    ha hb (scaled_root d s hd₀ hsroot) (scaled_root d t hd₀ htroot)
    ⟨haU, fun h => (upper haU).2.asymm (lower h).2,
      fixed_excludes_scaled hd (by norm_num) hr₁ (upper haU).1,
      fixed_excludes_scaled hd le_rfl hr₁ (upper haU).1⟩
    ⟨fun h => (lower hbL).2.asymm (upper h).2, hbL,
      fixed_excludes_scaled hd (by norm_num) hr₁ (lower hbL).1,
      fixed_excludes_scaled hd le_rfl hr₁ (lower hbL).1⟩
    ⟨notUpper _, notLower _, hG, sep hG, rfl⟩
    ⟨notUpper _, notLower _, fun h => sep h hH, hH, rfl⟩
  have g₁ : scaledDisk d 1 r = (fun z : ℂ => ‖z/(d:ℂ)+1‖ < r) := by
    funext z
    simp only [scaledDisk, Complex.ofReal_one]
  have g₂ : scaledDisk d (1/3) r = (fun z : ℂ => ‖z/(d:ℂ)+1/3‖ < r) := by
    funext z
    simp only [scaledDisk, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  obtain ⟨nA, nB, nG, nH, cover, reality⟩ := four
  have sameCount {P Q : ℂ → Prop} {iP : DecidablePred P} {iQ : DecidablePred Q}
      (n : (@Multiset.filter ℂ Q iQ (contactPencilPoly d).roots).card = 1)
      (h : ∀ z, P z ↔ Q z) :
      (@Multiset.filter ℂ P iP (contactPencilPoly d).roots).card = 1 :=
    (congrArg Multiset.card (@Multiset.filter_congr ℂ P Q iP iQ _ (fun z _ => h z))).trans n
  refine ⟨sameCount nA (fun _ => Iff.rfl), sameCount nB (fun _ => Iff.rfl),
    sameCount nG ?_, sameCount nH ?_, ?_, ?_⟩
  · rw [g₁]
    exact fun _ => Iff.rfl
  · rw [g₂]
    exact fun _ => Iff.rfl
  · simpa only [A, B, upperCenter, lowerCenter, g₁, g₂] using cover
  · simpa only [g₁, g₂] using reality

#print axioms quartic_pencil_large_parameter_roots

end Turan
