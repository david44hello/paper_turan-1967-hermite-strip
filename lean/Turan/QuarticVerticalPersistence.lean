module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.QuarticVerticalDefs
public import Turan.GeneralNodes
public import Turan.Rouche
public import Turan.Degree
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Filter Polynomial Set Metric
open scoped Topology
namespace Turan
namespace VerticalPersistence

/-- Disjoint neighborhoods with enough target entries provide a matching
of multisets of equal cardinality. -/
private theorem cluster_matching (M N : Multiset ℂ) (P : ℂ → ℂ → Prop) [∀ z, DecidablePred (P z)]
    (hc : M.card = N.card)
    (hsep : ∀ z ∈ M, ∀ t ∈ M, ∀ q, P z q → P t q → z = t)
    (hcount : ∀ z ∈ M, M.count z ≤ (N.filter (P z)).card) : Multiset.Rel P M N := by
  induction M using Multiset.induction_on generalizing N with
  | empty => simpa using hc.symm
  | cons z M ih =>
    have hp := hcount z (Multiset.mem_cons_self _ _)
    have hzlt : M.count z < (N.filter (P z)).card := by simpa using hp
    have hpos := (Nat.zero_le _).trans_lt hzlt
    obtain ⟨q,hq⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
    obtain ⟨hqN,hzq⟩ := Multiset.mem_filter.mp hq
    obtain ⟨N',rfl⟩ := Multiset.exists_cons_of_mem hqN
    apply Multiset.Rel.cons hzq
    apply ih _ (by simpa using hc)
      (fun t ht w hw => hsep t (Multiset.mem_cons_of_mem ht) w (Multiset.mem_cons_of_mem hw))
    intro t ht
    have h := hcount t (Multiset.mem_cons_of_mem ht)
    by_cases he : t = z
    · subst t
      simpa [hzq] using h
    · have hn : ¬ P t q := fun hq => he (hsep t (Multiset.mem_cons_of_mem ht) z
          (Multiset.mem_cons_self _ _) q hq hzq)
      simpa [hn,he,Ne.symm he] using h

private theorem move_bounds (z : ℂ) (hz : z.im ≠ 0) (e : ℝ) (he : 0 ≤ e) :
    |(quarticVerticalMove e z).im| = |z.im| + e ∧ dist (quarticVerticalMove e z) z = e := by
  rcases lt_or_gt_of_ne hz with hn | hp
  · have hs : z.im / |z.im| = -1 := by rw [abs_of_neg hn,div_neg,div_self hz]
    simp only [quarticVerticalMove,hs,mul_neg_one]
    constructor
    · have hi : (z + Complex.I * ((-e : ℝ) : ℂ)).im = z.im - e := by simp [Complex.mul_im, sub_eq_add_neg]
      rw [hi,abs_of_neg (by linarith),abs_of_neg hn]
      ring
    · simp [dist_eq_norm, abs_of_nonneg he]
  · have hs : z.im / |z.im| = 1 := by rw [abs_of_pos hp,div_self hz]
    simp only [quarticVerticalMove,hs,mul_one]
    simp [Complex.mul_im,dist_eq_norm,abs_of_nonneg he,abs_of_pos hp,
      abs_of_pos (show 0 < z.im+e by linarith)]

private theorem rows_give_root (c d w : ℂ) (hw : w ≠ 0)
    (hv : c * nodeMode 2 w + d * nodeMode 4 w = -2) :
    (family 2 4 c d).IsRoot (w-1/2) ∧
    (c*deriv (nodeMode 2) w + d*deriv (nodeMode 4) w = 0 →
      (family 2 4 c d).derivative.IsRoot (w-1/2)) := by
  let f := family 2 4 c d
  have hzero : 2 + c * nodeMode 2 w + d * nodeMode 4 w = 0 := by linear_combination hv
  refine ⟨by rw [IsRoot, family_node_form _ _ _ _ _ hw, hzero, mul_zero], ?_⟩
  intro ht
  have hn (j : ℕ) : DifferentiableAt ℂ (nodeMode j) w := by
    apply DifferentiableAt.div _ differentiableAt_id hw
    exact ((hermite j).differentiableAt).comp w (differentiableAt_id.sub_const _)
  have hg := (hasDerivAt_id w).mul (((hasDerivAt_const w (2:ℂ)).add
    ((hn 2).hasDerivAt.const_mul c)).add ((hn 4).hasDerivAt.const_mul d))
  have hlocal : (fun x => f.eval (x-1/2)) =ᶠ[𝓝 w]
      (fun x => x*(2+c*nodeMode 2 x+d*nodeMode 4 x)) := by
    filter_upwards [eventually_ne_nhds hw] with x hx using family_node_form 2 4 c d x hx
  have hp := (f.hasDerivAt (w-1/2)).comp w ((hasDerivAt_id w).sub_const (1/2))
  have h := hp.unique (hg.congr_of_eventuallyEq hlocal)
  simpa [id,hzero,ht] using h

private theorem disk_count (a b z : ℂ) (r : ℝ) (hr : 0 < r)
    (hfree : ∀ q ∈ sphere z r, (family 2 4 a b).eval q ≠ 0) :
    ∀ᶠ cd : ℂ × ℂ in 𝓝 (a,b),
      ((family 2 4 cd.1 cd.2).roots.filter (fun q => dist q z < r)).card =
      ((family 2 4 a b).roots.filter (fun q => dist q z < r)).card := by
  let G := {x : (ℂ × ℂ) × ℂ | ‖(family 2 4 x.1.1 x.1.2).eval x.2 -
    (family 2 4 a b).eval x.2‖ < ‖(family 2 4 a b).eval x.2‖}
  have hopen : IsOpen G := by
    apply isOpen_lt
    · simp only [family,eval_add,eval_mul,eval_C,eval_X,eval_ofNat,eval_one]
      fun_prop
    · exact ((family 2 4 a b).continuous.comp continuous_snd).norm
  have hsub : ({(a,b)} : Set (ℂ × ℂ)) ×ˢ sphere z r ⊆ G := by
    rintro ⟨v,w⟩ ⟨(rfl : v = (a,b)), hw⟩
    simpa [G] using norm_pos_iff.mpr (hfree w hw)
  obtain ⟨U,V,hU,_,ha,hV,hUV⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_sphere z r) hopen hsub
  filter_upwards [hU.mem_nhds (singleton_subset_iff.mp ha)] with cd hcd
  exact polynomial_rouche _ _ z r hr (fun q hq => hUV (mk_mem_prod hcd (hV hq)))

private theorem small_radius (M : Multiset ℂ) (y δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r < δ ∧
      (∀ z ∈ M, ∀ t ∈ M, z ≠ t → 2*r < dist z t) ∧
      (∀ z ∈ M, y < |z.im| → 2*r < |z.im|-y) := by
  classical
  let l := 𝓝[>] (0 : ℝ)
  have small {x : ℝ} (hx : 0 < x) : ∀ᶠ r in l, 2*r < x := by
    filter_upwards [(gt_mem_nhds (half_pos hx)).filter_mono nhdsWithin_le_nhds] with r hr
    change r < x/2 at hr
    linarith
  have hs : ∀ᶠ r in l, ∀ z ∈ M.toFinset, ∀ t ∈ M.toFinset, z ≠ t → 2*r < dist z t := by
    apply (eventually_all_finset _).2
    intro z _
    apply (eventually_all_finset _).2
    intro t _
    by_cases h : z = t
    · simp [h]
    · exact (small (dist_pos.mpr h)).mono fun _ hr _ => hr
  have hg : ∀ᶠ r in l, ∀ z ∈ M.toFinset, y < |z.im| → 2*r < |z.im|-y := by
    apply (eventually_all_finset _).2
    intro z _
    by_cases h : y < |z.im|
    · exact (small (sub_pos.mpr h)).mono fun _ hr _ => hr
    · simp [h]
  have hpos : ∀ᶠ r in l, 0 < r := self_mem_nhdsWithin
  obtain ⟨r,hr,hδ',hr₁,hr₂⟩ := (hpos.and
    (((gt_mem_nhds hδ).filter_mono nhdsWithin_le_nhds).and (hs.and hg))).exists
  exact ⟨r,hr,hδ',by simpa using hr₁,by simpa using hr₂⟩

end VerticalPersistence

open VerticalPersistence in
theorem quartic_vertical_persistence (a b : ℂ) (hb : b ≠ 0) (y : ℝ) (hy : 0 < y)
    (hlow : ∀ z : ℂ, (family 2 4 a b).eval z = 0 → y ≤ |z.im|)
    (hfew : (quarticBoundaryRoots a b y).card ≤ 2) (A B : ℝ → ℂ)
    (hA : Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 a)) (hB : Tendsto B (𝓝[>] (0 : ℝ)) (𝓝 b))
    (hrows : ∀ᶠ ε in 𝓝[>] (0 : ℝ), quarticMovedRows (quarticBoundaryRoots a b y) ε (A ε) (B ε)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      let F := family 2 4 (A ε) (B ε)
      let moved := (quarticBoundaryRoots a b y).map (quarticVerticalMove ε)
      let oldRest := (family 2 4 a b).roots.filter (fun z => y < |z.im|)
      F.natDegree = 4 ∧ quarticBoundaryRoots (A ε) (B ε) (y + ε) = moved ∧
        (∃ R : Multiset ℂ, F.roots = moved + R ∧
          Multiset.Rel (fun z z' : ℂ => dist z z' < δ) oldRest R ∧
          ∀ z ∈ R, y + ε < |z.im|) ∧
        (∀ z : ℂ, F.eval z = 0 → y < |z.im|) := by
  classical
  intro δ hδ
  let f := family 2 4 a b
  let M := quarticBoundaryRoots a b y
  let S := f.roots.filter (fun z => y < |z.im|)
  have hdeg {c d : ℂ} (hd : d ≠ 0) : (family 2 4 c d).natDegree = 4 := by
    simp [family_degree 2 4 (by decide) (by decide), hd]
  have hne {c d : ℂ} (hd : d ≠ 0) : family 2 4 c d ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (family 2 4 c d).natDegree by rw [hdeg hd]; decide)
  have oldsplit : M + S = f.roots := by
    have hs : S = f.roots.filter (fun z => ¬ |z.im| = y) := by
      apply Multiset.filter_congr
      intro z hz
      have h := hlow z (isRoot_of_mem_roots hz)
      exact ⟨fun ht => ht.ne', fun hn => lt_of_le_of_ne h (Ne.symm hn)⟩
    rw [hs]
    exact Multiset.filter_add_not _ _
  obtain ⟨r,hr,hrδ,hsep,hgap⟩ := small_radius f.roots y δ hδ
  have Hdisk : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ z ∈ f.roots.toFinset,
      (((family 2 4 (A ε) (B ε)).roots).filter (fun q => dist q z < r)).card =
        f.roots.count z := by
    apply (eventually_all_finset _).2
    intro z hz
    have hz' := Multiset.mem_toFinset.mp hz
    have iso (q : ℂ) (hq : q ∈ f.roots) (hd : dist q z ≤ r) : q = z := by
      by_contra hn
      linarith only [hsep q hq z hz' hn,hd,hr]
    have hfree (q : ℂ) (hq : q ∈ sphere z r) : f.eval q ≠ 0 := by
      intro he
      have hd := mem_sphere.mp hq
      have hmem := (mem_roots (hne hb)).mpr he
      rw [iso q hmem hd.le, dist_self] at hd
      exact hr.ne hd
    have hfilter : f.roots.filter (fun q => dist q z < r) = f.roots.filter (· = z) := by
      apply Multiset.filter_congr
      exact fun q hq => ⟨fun hd => iso q hq hd.le,fun e => by simpa [e] using hr⟩
    have H := (hA.prodMk_nhds hB).eventually (disk_count a b z r hr hfree)
    filter_upwards [H] with ε hε
    change _ = (f.roots.filter (fun q => dist q z < r)).card at hε
    rw [hfilter, Multiset.filter_eq', Multiset.card_replicate] at hε
    exact hε
  filter_upwards [Hdisk,hrows,hB.eventually_ne hb, self_mem_nhdsWithin,
    (gt_mem_nhds hr).filter_mono nhdsWithin_le_nhds] with ε hdis heq hb' hεpos hεlt
  change 0 < ε at hεpos
  change ε < r at hεlt
  let F := family 2 4 (A ε) (B ε)
  let move := quarticVerticalMove ε
  let P (z q : ℂ) := dist q z < r ∧ (|z.im| = y → q = move z)
  have hmove (z : ℂ) (hc : |z.im| = y) :
      |(move z).im| = y+ε ∧ dist (move z) z = ε := by
    have hn : z.im ≠ 0 := fun he => by simp [he] at hc; linarith
    simpa [move,hc] using move_bounds z hn ε hεpos.le
  have hmult (z : ℂ) (hz : z ∈ f.roots) (hc : |z.im| = y) :
      f.roots.count z ≤ F.roots.count (move z) := by
    have hzM : z ∈ M := Multiset.mem_filter.mpr ⟨hz,hc⟩
    have hcnt : M.count z = f.roots.count z := Multiset.count_filter_of_pos hc
    have hm := heq z hzM
    let w := move z + 1/2
    have hw : w ≠ 0 := by
      intro hh
      have hs : (move z).im = 0 := by simpa [w] using congrArg Complex.im hh
      have := (hmove z hc).1
      rw [hs,abs_zero] at this
      linarith
    have h := rows_give_root (A ε) (B ε) w hw hm.1
    have hw' : w-1/2 = move z := by simp [w]
    rw [hw'] at h
    change _ ≤ (family 2 4 (A ε) (B ε)).roots.count _
    rw [← hcnt, count_roots (family 2 4 (A ε) (B ε))]
    have hcap := (Multiset.count_le_card z M).trans hfew
    by_cases hdouble : 2 ≤ M.count z
    · have hh := (one_lt_rootMultiplicity_iff_isRoot (hne hb')).2 ⟨h.1,h.2 (hm.2 hdouble)⟩
      exact hcap.trans hh
    · have hh := rootMultiplicity_pos (hne hb') |>.mpr h.1
      exact (show M.count z ≤ 1 by omega).trans hh
  have rel : Multiset.Rel P f.roots F.roots := by
    apply cluster_matching
    · rw [← (IsAlgClosed.splits f).natDegree_eq_card_roots,
        ← (IsAlgClosed.splits F).natDegree_eq_card_roots]
      exact (hdeg hb).trans (hdeg hb').symm
    · intro z hz t ht q hzq htq
      by_contra h
      have h₁ := hzq.1
      have h₂ := htq.1
      have hd := dist_triangle_left z t q
      linarith only [hd,h₁,h₂,hsep z hz t ht h]
    · intro z hz
      by_cases hc : |z.im| = y
      · have hf : F.roots.filter (P z) = F.roots.filter (· = move z) := by
          apply Multiset.filter_congr
          exact fun q _ => ⟨fun h => h.2 hc, fun e => ⟨e ▸ (hmove z hc).2.trans_lt hεlt,fun _ => e⟩⟩
        rw [hf,Multiset.filter_eq',Multiset.card_replicate]
        exact hmult z hz hc
      · have hf : F.roots.filter (P z) = F.roots.filter (fun q => dist q z < r) := by
          apply Multiset.filter_congr
          simp [P,hc]
        rw [hf]
        exact (hdis z (Multiset.mem_toFinset.mpr hz)).ge
  rw [← oldsplit] at rel
  obtain ⟨T,R,hT,hR,hparts⟩ := Multiset.rel_add_left.mp rel
  have hT' : M.map move = T := Multiset.rel_eq.mp <| Multiset.rel_map_left.mpr <|
    hT.mono fun z hz q _ h => (h.2 (Multiset.mem_filter.mp hz).2).symm
  rw [← hT'] at hparts
  have far (q : ℂ) (hq : q ∈ R) : y+ε < |q.im| := by
    obtain ⟨z,hz,hzq⟩ := Multiset.exists_mem_of_rel_of_mem (Multiset.rel_flip.mpr hR) hq
    have hg := hgap z (Multiset.mem_filter.mp hz).1 (Multiset.mem_filter.mp hz).2
    have hd : dist q z < r := hzq.1
    have hi := Complex.abs_im_le_norm (z-q)
    rw [Complex.sub_im,← dist_eq_norm,dist_comm z q] at hi
    have htri : |z.im| ≤ |z.im-q.im| + |q.im| := by
      simpa using abs_add_le (z.im-q.im) q.im
    linarith
  have moved_height (q : ℂ) (hq : q ∈ M.map move) : |q.im| = y+ε := by
    obtain ⟨z,hz,rfl⟩ := Multiset.mem_map.mp hq
    exact (hmove z (Multiset.mem_filter.mp hz).2).1
  refine ⟨hdeg hb',?_,⟨R,hparts,hR.mono (fun z _ q _ h => (dist_comm z q).trans_lt (h.1.trans hrδ)),far⟩,?_⟩
  · change F.roots.filter _ = M.map move
    rw [hparts,Multiset.filter_add,Multiset.filter_eq_self.mpr moved_height,
      Multiset.filter_eq_nil.mpr (fun z hz => (far z hz).ne'), add_zero]
  · intro z hz
    have hzm : z ∈ F.roots := (mem_roots (hne hb')).mpr hz
    rw [hparts,Multiset.mem_add] at hzm
    rcases hzm with hm | hr'
    · rw [moved_height z hm]; linarith
    · linarith only [far z hr', hεpos]

#print axioms quartic_vertical_persistence
end Turan
