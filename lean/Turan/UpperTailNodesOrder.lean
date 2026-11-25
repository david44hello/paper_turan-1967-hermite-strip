-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.UpperTailNodesScalar
import Turan.TailNodesGeometry

noncomputable section
open Set Polynomial
namespace Turan.UpperTailNodes

/-- Enumerate the least available positive distances, keeping their exact ranks.
The occupied interval following the current node bounds the next step. -/
private theorem sorted_distances (S : Finset ℝ) (h : ℝ) (N : ℕ) (hh : 0 < h)
    (hN : 0 < N) (hNh : (N:ℝ)*h ≤ 3) (hs : ∀ t ∈ S, 0 < t)
    (cell : ∀ x : ℝ, 0 ≤ x → x+h ≤ 3 → ∃ t ∈ S, x < t ∧ t < x+h) :
    ∃ d : Fin N → ℝ, StrictMono d ∧
      (∀ i, d i ∈ S ∧ d i ∈ Ioc 0 3 ∧ (S.filter (· < d i)).card = i.val ∧
        d i ≤ d ⟨0,hN⟩ + (i.val:ℝ)*h) ∧
      d ⟨0,hN⟩ < h ∧ (∀ t ∈ S, d ⟨0,hN⟩ ≤ t) ∧
      ∀ i k : Fin N, k.val = i.val+1 → d k ≤ d i+h := by
  classical
  let next (x : ℝ) := if hy : (S.filter (x < ·)).Nonempty then (S.filter (x < ·)).min' hy else x
  have step (x : ℝ) (hx : 0 ≤ x) (hbound : x+h ≤ 3) :
      next x ∈ S ∧ x < next x ∧ next x < x+h ∧ ∀ y ∈ S, x < y → next x ≤ y := by
    obtain ⟨t, ht, hxt, htx⟩ := cell x hx hbound
    have ht' := Finset.mem_filter.mpr (And.intro ht hxt)
    have hne : (S.filter (x < ·)).Nonempty := ⟨t, ht'⟩
    simp only [next, dif_pos hne]
    obtain ⟨hm,hgt⟩ := Finset.mem_filter.mp ((S.filter (x < ·)).min'_mem hne)
    exact ⟨hm, hgt, ((S.filter (x < ·)).min'_le t ht').trans_lt htx,
      fun y hy hxy => (S.filter (x < ·)).min'_le y (Finset.mem_filter.mpr ⟨hy,hxy⟩)⟩
  let D (i : ℕ) := next^[i+1] 0
  have succD (i : ℕ) : D (i+1) = next (D i) := Function.iterate_succ_apply' .. 
  have budget (i : ℕ) (hi : i < N) : ((i:ℝ)+1)*h ≤ 3 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hi : (i:ℝ)+1 ≤ N) hh.le).trans hNh
  have base := step 0 le_rfl (by simpa using budget 0 hN)
  change D 0 ∈ S ∧ 0 < D 0 ∧ D 0 < 0+h ∧ ∀ y ∈ S, 0 < y → D 0 ≤ y at base
  have hfirst : D 0 < h := by simpa using base.2.2.1
  have hmin (t : ℝ) (ht : t ∈ S) := base.2.2.2 t ht (hs t ht)
  have bound (i : ℕ) (hi : i < N) : D i ∈ S ∧ (S.filter (· < D i)).card = i ∧
      D i ≤ D 0 + (i:ℝ)*h := by
    induction i with
    | zero =>
      exact ⟨base.1, Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr
        (fun y hy => (hmin y hy).not_gt)), by simp⟩
    | succ i ih =>
      obtain ⟨hiS, hrank, hd⟩ := ih (by omega)
      have hb := budget (i+1) hi
      push_cast at hb
      obtain ⟨hy,hxy,hyh,hnext⟩ := step (D i) (hs _ hiS).le (by linarith)
      rw [succD]
      have hf : S.filter (· < next (D i)) = insert (D i) (S.filter (· < D i)) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hys,hlt⟩
          rcases lt_trichotomy y (D i) with hl | he | hg
          · exact Or.inr ⟨hys,hl⟩
          · exact Or.inl he
          · exact (hlt.not_ge (hnext y hys hg)).elim
        · rintro (rfl | ⟨hys,hy'⟩)
          · exact ⟨hiS,hxy⟩
          · exact ⟨hys,hy'.trans hxy⟩
      refine ⟨hy, ?_, ?_⟩
      · rw [hf, Finset.card_insert_of_notMem (by simp), hrank]
      · push_cast; linarith
  let d (i : Fin N) := D i.val
  refine ⟨d, ?_, ?_, hfirst, hmin, ?_⟩
  · intro i k hik
    by_contra! hle
    have hc := Finset.card_le_card (show S.filter (· < D k.val) ⊆ S.filter (· < D i.val) from
      fun _ hx => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
        lt_of_lt_of_le (Finset.mem_filter.mp hx).2 hle⟩)
    rw [(bound _ k.isLt).2.1, (bound _ i.isLt).2.1] at hc
    exact (Nat.not_le_of_lt hik) hc
  · intro i
    obtain ⟨hi,hc,hb⟩ := bound _ i.isLt
    have hbud := budget _ i.isLt
    exact ⟨hi, ⟨hs _ hi, by dsimp [d]; linarith⟩, hc, hb⟩
  · intro i k heq
    have hb := budget k.val k.isLt
    rw [heq, Nat.cast_succ] at hb
    obtain ⟨hiS,_,hd⟩ := bound _ i.isLt
    dsimp only [d]
    rw [heq, succD]
    exact (step _ (hs _ hiS).le (by linarith)).2.2.1.le

private def side (j : ℕ) (s : ℝ) : Finset ℝ :=
  ((hermite j).roots.toFinset.filter (fun z => z.im = 0 ∧ 0 < s*(z.re-center))).image
    (fun z => s*(z.re-center))

private theorem side_rank (j : ℕ) {s : ℝ} (hs : s ≠ 0) (t : ℝ) :
    ((side j s).filter (· < t)).card = nearer j s t := by
  classical
  unfold side nearer
  rw [Finset.filter_image, Finset.card_image_of_injOn]
  · congr 1
    ext z
    simp [Finset.mem_filter, and_assoc]
  · intro z hz w hw he
    have hz' := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2.1
    have hw' := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2.1
    exact Complex.ext (by dsimp at he; exact sub_left_inj.mp (mul_left_cancel₀ hs he)) (hz'.trans hw'.symm)

private theorem side_mem (j : ℕ) (h0 : psi j (-1/2) ≠ 0) {s : ℝ} (hs : s=1 ∨ s= -1) (t : ℝ) :
    t ∈ side j s ↔ 0 < t ∧ psi j ((center+s*t : ℝ) : ℂ) = 0 := by
  classical
  have hsq : s^2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hpoly : hermite j ≠ 0 := fun h => h0 (by simp [psi,h])
  have hden : (Real.sqrt (2^j*(j.factorial:ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < 2^j*(j.factorial:ℝ))).ne'
  constructor
  · rintro ht
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hzr, him, hpos⟩ := Finset.mem_filter.mp hz
    have he : ((center+s*(s*(z.re-center)) : ℝ) : ℂ) = z := Complex.ext
      (by simp only [Complex.ofReal_re]; linear_combination (z.re-center)*hsq) (by simpa using him.symm)
    exact ⟨hpos, by rw [he, psi, isRoot_of_mem_roots (Multiset.mem_toFinset.mp hzr), zero_div]⟩
  · rintro ⟨ht,hz⟩
    let z : ℂ := ((center+s*t : ℝ) : ℂ)
    have hz' : (hermite j).eval z = 0 := (div_eq_zero_iff.mp hz).resolve_right hden
    have he : s*(z.re-center) = t := by dsimp [z]; linear_combination t*hsq
    exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr ((mem_roots hpoly).mpr hz'), rfl, he ▸ ht⟩, he⟩

theorem ordered_nodes (j : ℕ) (hj : 225 ≤ j) (h0 : psi j (-1/2) ≠ 0) :
    0 < nodeCount j ∧ ∃ d e : Fin (nodeCount j) → ℝ, StrictMono d ∧ StrictMono e ∧
    (∀ i, d i ∈ Ioc 0 3 ∧ e i ∈ Ioc 0 3 ∧
      psi j ((center+d i : ℝ) : ℂ) = 0 ∧ psi j ((center-e i : ℝ) : ℂ) = 0 ∧
      nearer j 1 (d i) = i.val ∧ nearer j (-1) (e i) = i.val ∧
      d i + e i ≤ (2*(i.val:ℝ)+1)*eta j) ∧
    (∀ i : Fin (nodeCount j), i.val = 0 → d i < eta j ∧ e i < eta j ∧ d i+e i ≤ eta j) ∧
    (∀ i k : Fin (nodeCount j), k.val = i.val+1 → d k ≤ d i+eta j ∧ e k ≤ e i+eta j) := by
  classical
  let h := eta j
  let N := nodeCount j
  obtain ⟨hh, hu⟩ := eta_bounds j hj
  change 0 < h at hh
  change h < 0.151 at hu
  have hN : 0 < N := by
    change 1 ≤ ⌊3/h⌋₊
    apply Nat.le_floor
    push_cast
    rw [le_div_iff₀ hh]
    linarith
  have hNh : (N:ℝ)*h ≤ 3 := (le_div_iff₀ hh).mp (Nat.floor_le (by positivity : 0 ≤ 3/h))
  let k := Real.sqrt (2*(j:ℝ)-11.25)
  have hj' : (225:ℝ) ≤ j := by exact_mod_cast hj
  have hrad : 0 < 2*(j:ℝ)-11.25 := by linarith
  have hcell (x : ℝ) (hl : center-3 ≤ x) (hr : x+h ≤ center+3) :
      ∃ u ∈ Ioo x (x+h), psi j (u:ℂ) = 0 := by
    apply hermite_sturm_interval j x k (Real.sqrt_pos.mpr hrad)
    intro t ht
    have ht₁ : -(7:ℝ)/2 < t := by unfold center at hl; linarith [ht.1]
    have ht₂ : t < 7/2 := by
      have htx : t < x+h := ht.2
      unfold center at hr
      linarith
    dsimp [k]
    nlinarith only [Real.sq_sqrt hrad.le, mul_pos (by linarith only [ht₁] : 0 < 7/2+t)
      (sub_pos.mpr ht₂)]
  have occupied (s : ℝ) (hs : s=1 ∨ s= -1) (x : ℝ) (hx : 0 ≤ x) (hb : x+h ≤ 3) :
      ∃ t ∈ side j s, x < t ∧ t < x+h := by
    rcases hs with rfl | rfl
    · obtain ⟨u,⟨hl,hr⟩,hz⟩ := hcell (center+x) (by linarith) (by linarith)
      exact ⟨u-center, (side_mem j h0 (Or.inl rfl) _).mpr ⟨by linarith, by simpa using hz⟩,
        by linarith, by linarith⟩
    · obtain ⟨u,⟨hl,hr⟩,hz⟩ := hcell (center-x-h) (by linarith) (by linarith)
      exact ⟨center-u, (side_mem j h0 (Or.inr rfl) _).mpr ⟨by linarith, by simpa using hz⟩,
        by linarith, by linarith⟩
  obtain ⟨d,hd,hdp,hdh,hdmin,hdnext⟩ := sorted_distances (side j 1) h N hh hN hNh
    (fun t ht => ((side_mem j h0 (Or.inl rfl) t).mp ht).1) (occupied 1 (Or.inl rfl))
  obtain ⟨e,he,hep,heh,hemin,henext⟩ := sorted_distances (side j (-1)) h N hh hN hNh
    (fun t ht => ((side_mem j h0 (Or.inr rfl) t).mp ht).1) (occupied (-1) (Or.inr rfl))
  let o : Fin N := ⟨0,hN⟩
  have pairs := tail_node_pairs j hj h0
  dsimp only at pairs
  rw [show Real.pi / Real.sqrt (2*(j:ℝ)-1125/100) = eta j by norm_num [eta]] at pairs
  obtain ⟨d',e',_,_,hp⟩ := pairs
  obtain ⟨hd',he',hr,hl,hb⟩ := hp o
  have hroot {z : ℂ} (hz : z ∈ (hermite j).roots.toFinset.filter
      (fun s => s.im = 0 ∧ -(7:ℝ)/2 ≤ s.re ∧ s.re ≤ 5/2)) : psi j z = 0 := by
    rw [psi, isRoot_of_mem_roots (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hz).1), zero_div]
  have hdr := hdmin _ ((side_mem j h0 (Or.inl rfl) _).mpr ⟨hd', by simpa [center] using hroot hr⟩)
  have hel := hemin _ ((side_mem j h0 (Or.inr rfl) _).mpr ⟨he', by simpa [center,sub_eq_add_neg] using hroot hl⟩)
  have hpair₀ : d o + e o ≤ h := by
    change d o ≤ d' o at hdr
    change e o ≤ e' o at hel
    exact (add_le_add hdr hel).trans (by simpa [o,h,eta] using hb)
  refine ⟨hN, d, e, hd, he, ?_, ?_, fun i l hil => ⟨hdnext i l hil, henext i l hil⟩⟩
  · intro i
    obtain ⟨hdS,hdI,hdrank,hdb⟩ := hdp i
    obtain ⟨heS,heI,herank,heb⟩ := hep i
    refine ⟨hdI, heI, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using ((side_mem j h0 (Or.inl rfl) _).mp hdS).2
    · simpa [sub_eq_add_neg] using ((side_mem j h0 (Or.inr rfl) _).mp heS).2
    · exact (side_rank j one_ne_zero _).symm.trans hdrank
    · exact (side_rank j (neg_ne_zero.mpr one_ne_zero) _).symm.trans herank
    · change d i ≤ d o + (i.val:ℝ)*h at hdb
      change e i ≤ e o + (i.val:ℝ)*h at heb
      change d i+e i ≤ (2*(i.val:ℝ)+1)*h
      linarith only [hdb, heb, hpair₀]
  · intro i hi
    have heq : i = o := Fin.ext hi
    subst i
    exact ⟨hdh,heh,hpair₀⟩

end Turan.UpperTailNodes
