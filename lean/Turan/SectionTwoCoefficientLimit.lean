module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.SectionTwoSelection
public import Turan.Degree

@[expose] public section

noncomputable section
open Polynomial Filter Metric
open scoped Topology BigOperators Classical
namespace Turan.SectionTwo
variable {s : ℕ}

/-- A nonzero coefficient of positive Hermite degree forces a nonconstant sum. -/
private theorem positive_slot_degree (k : Fin s → ℕ) (hk : Function.Injective k)
    (b : Fin s → ℂ) (v : Fin s) (hv : 0 < k v) (hb : b v ≠ 0) : 0 < (slotSum k b).natDegree := by
  let f (t : Fin s) := C (b t) * hermite (k t)
  have hdeg {t : Fin s} (ht : b t ≠ 0) : (f t).natDegree = k t := by
    dsimp only [f]
    rw [natDegree_C_mul ht, (hermite_degree _).1]
  have hn {t : Fin s} (ht : f t ≠ 0) : b t ≠ 0 := fun h => ht (by simp [f, h])
  change 0 < (∑ t, f t).natDegree
  rw [natDegree_sum_eq_of_disjoint]
  · exact (hv.trans_eq (hdeg hb).symm).trans_le (Finset.le_sup (f := fun t => (f t).natDegree) (Finset.mem_univ v))
  · intro i hi j hj hij
    change (f i).natDegree ≠ (f j).natDegree
    rw [hdeg (hn hi.2), hdeg (hn hj.2)]
    exact hk.ne hij

private theorem sum_limit (k : Fin s → ℕ) (a : ℕ → Fin s → ℂ) (d : ℕ → ℂ)
    (b : Fin s → ℂ) (h : ∀ v, Tendsto (fun j => a j v/d j) atTop (𝓝 (b v))) :
    TendstoLocallyUniformly (fun j z => (slotSum k (a j)).eval z/d j)
      (fun z => (slotSum k b).eval z) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro z
  have hlim : Tendsto (fun p : ℕ × ℂ => ∑ v, (a p.1 v/d p.1)*(hermite (k v)).eval p.2)
      (atTop ×ˢ 𝓝 z) (𝓝 ((slotSum k b).eval z)) := by
    simp only [slotSum, eval_finsetSum, eval_mul, eval_C]
    apply tendsto_finsetSum
    intro v _
    exact ((h v).comp tendsto_fst).mul ((hermite (k v)).continuous.continuousAt.tendsto.comp tendsto_snd)
  have hleft : Tendsto (fun p : ℕ × ℂ => (slotSum k b).eval p.2) (atTop ×ˢ 𝓝 z)
      (𝓝 ((slotSum k b).eval z)) := (slotSum k b).continuous.continuousAt.tendsto.comp tendsto_snd
  apply ((hleft.prodMk_nhds hlim).mono_right (nhds_le_uniformity _)).congr'
  exact Eventually.of_forall fun p => by
    simp only [slotSum, eval_finsetSum, eval_mul, eval_C, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem largest_coefficient_limit (hs : s ∈ Set.Icc 2 4) (k : Fin s → ℕ)
    (hk : Function.Injective k) (v₀ v₁ : Fin s) (h₀ : k v₀ = 0) (h₁ : k v₁ = 1)
    (a : ℕ → Fin s → ℂ) (hc : Tendsto (fun j => a j v₀) atTop (𝓝 1))
    (hd : Tendsto (fun j => a j v₁) atTop (𝓝 1)) :
    ∃ (φ : ℕ → ℕ) (t : Fin s) (b : Fin s → ℂ), StrictMono φ ∧
      (∀ j, a (φ j) t ≠ 0 ∧ ∀ v, ‖a (φ j) v‖ ≤ ‖a (φ j) t‖) ∧ b t = 1 ∧
      (∀ v, Tendsto (fun j => a (φ j) v / a (φ j) t) atTop (𝓝 (b v))) ∧
      TendstoLocallyUniformly (fun j z => (slotSum k (a (φ j))).eval z / a (φ j) t)
        (fun z => (slotSum k b).eval z) atTop ∧
      ((∃ C₀ : ℝ, ∃ᶠ j in atTop, ∀ v, ‖a j v‖ ≤ C₀) →
        ∃ C₀ : ℝ, ∀ j v, ‖a (φ j) v‖ ≤ C₀) ∧
      (((∃ C₀ : ℝ, ∀ j v, ‖a (φ j) v‖ ≤ C₀) ∧ b v₁ ≠ 0) ∨
        (Tendsto (fun j => ‖a (φ j) t‖) atTop atTop ∧ b v₀ = 0 ∧ b v₁ = 0 ∧
          ∃ v, 2 ≤ k v ∧ ‖b v‖ = 1)) ∧ 0 < (slotSum k b).natDegree := by
  letI : Nonempty (Fin s) := ⟨v₀⟩
  choose pivot _ hmax using fun j => Finset.exists_max_image Finset.univ
    (fun v : Fin s => ‖a j v‖) Finset.univ_nonempty
  let mag (j : ℕ) := ‖a j (pivot j)‖
  let bounded := ∃ C₀ : ℝ, ∃ᶠ j in atTop, ∀ v, ‖a j v‖ ≤ C₀
  have hpos : ∀ᶠ j in atTop, 0 < mag j :=
    (hd.eventually_ne one_ne_zero).mono fun j hj =>
      (norm_pos_iff.mpr hj).trans_le (hmax j v₁ (Finset.mem_univ _))
  have choose_branch : ∃ σ : ℕ → ℕ, StrictMono σ ∧ (∀ j, 0 < mag (σ j)) ∧
      (bounded → ∃ C₀ : ℝ, ∀ j v, ‖a (σ j) v‖ ≤ C₀) ∧
      (¬bounded → Tendsto (mag ∘ σ) atTop atTop) := by
    by_cases hb : bounded
    · obtain ⟨C₀, hC⟩ := hb
      have hbounded : bounded := ⟨C₀,hC⟩
      obtain ⟨σ,hσ,hh⟩ := extraction_of_frequently_atTop (hC.and_eventually hpos)
      exact ⟨σ,hσ,fun j => (hh j).2,fun _ => ⟨C₀,fun j => (hh j).1⟩,fun h => (h hbounded).elim⟩
    · obtain ⟨σ,hσ,hh⟩ := extraction_of_eventually_atTop hpos
      have hdiv : Tendsto mag atTop atTop := tendsto_atTop.mpr fun C₀ => by
        apply Eventually.mono (not_frequently.mp (show ¬∃ᶠ j in atTop, mag j ≤ C₀ from
          fun hh => hb ⟨C₀, hh.mono (fun j hj v => (hmax j v (Finset.mem_univ _)).trans hj)⟩))
        intro j hj
        exact le_of_not_ge hj
      exact ⟨σ,hσ,hh,fun h => (hb h).elim, fun _ => hdiv.comp hσ.tendsto_atTop⟩
  obtain ⟨σ,hσ,hpos,hbounded,hdiv⟩ := choose_branch
  have hf : ∃ᶠ j in atTop, ∃ t : Fin s, pivot (σ j) = t := Frequently.of_forall fun j => ⟨_,rfl⟩
  obtain ⟨t, ht⟩ := frequently_exists.mp hf
  obtain ⟨τ,hτ,hfix⟩ := extraction_of_frequently_atTop ht
  let ψ := σ ∘ τ
  have hmax' (j v) : ‖a (ψ j) v‖ ≤ ‖a (ψ j) t‖ := by
    simpa only [ψ, Function.comp_apply, hfix] using hmax (σ (τ j)) v (Finset.mem_univ _)
  have hne (j) : a (ψ j) t ≠ 0 := norm_pos_iff.mp (by
    simpa only [mag, ψ, Function.comp_apply, hfix] using hpos (τ j))
  let x (j : ℕ) (v : Fin s) : closedBall (0 : ℂ) 1 :=
    ⟨a (ψ j) v / a (ψ j) t, by
      rw [mem_closedBall, dist_zero_right, norm_div, div_le_one (norm_pos_iff.mpr (hne j))]
      exact hmax' j v⟩
  obtain ⟨g,ρ,hρ,hlim⟩ := CompactSpace.tendsto_subseq x
  let φ := ψ ∘ ρ
  let b (v : Fin s) : ℂ := g v
  have hφ : StrictMono φ := (hσ.comp hτ).comp hρ
  have hq (v) : Tendsto (fun j => a (φ j) v / a (φ j) t) atTop (𝓝 (b v)) :=
    (continuous_subtype_val.tendsto _).comp (tendsto_pi_nhds.mp hlim v)
  have hbt : b t = 1 := tendsto_nhds_unique (hq t) (by simpa [φ, hne] using
    (tendsto_const_nhds (x := (1 : ℂ)) (f := atTop (α := ℕ))))
  have hbound (hb : bounded) : ∃ C₀ : ℝ, ∀ j v, ‖a (φ j) v‖ ≤ C₀ := by
    obtain ⟨C₀, hC⟩ := hbounded hb
    exact ⟨C₀, fun j => hC (τ (ρ j))⟩
  refine ⟨φ,t,b,hφ,fun j => ⟨hne _, hmax' _⟩,hbt,hq,sum_limit _ _ _ _ hq,hbound,?_⟩
  by_cases hb : bounded
  · obtain ⟨C₀,hC⟩ := hbound hb
    have hb1 : b v₁ ≠ 0 := by
      intro hzero
      have hle (j) : ‖a (φ j) v₁‖ ≤ ‖a (φ j) v₁/a (φ j) t‖ * C₀ := by
        calc _ = ‖(a (φ j) v₁/a (φ j) t)*a (φ j) t‖ := by rw [div_mul_cancel₀ _ (show a (φ j) t ≠ 0 from hne (ρ j))]
             _ ≤ _ := by rw [norm_mul]; gcongr; apply hC
      have lin := le_of_tendsto_of_tendsto' (hd.comp hφ.tendsto_atTop).norm
        ((hq v₁).norm.mul_const C₀) hle
      simp [hzero] at lin
      norm_num at lin
    exact ⟨Or.inl ⟨⟨C₀,hC⟩,hb1⟩,positive_slot_degree k hk b v₁ (by omega) hb1⟩
  · have hdt : Tendsto (fun j => ‖a (φ j) t‖) atTop atTop := by
      simpa only [φ, ψ, mag, Function.comp_def, hfix] using
        (hdiv hb).comp (hτ.comp hρ).tendsto_atTop
    have vanish (v) (hv : Tendsto (fun j => a j v) atTop (𝓝 1)) : b v = 0 := by
      apply norm_eq_zero.mp
      apply tendsto_nhds_unique (hq v).norm
      simpa only [Function.comp_def, norm_div] using (hv.comp hφ.tendsto_atTop).norm.div_atTop hdt
    have hb0 := vanish v₀ hc
    have hb1 := vanish v₁ hd
    have hkt : 2 ≤ k t := by
      have hne0 : k t ≠ k v₀ := fun h => one_ne_zero ((hbt.symm.trans (congrArg b (hk h))).trans hb0)
      have hne1 : k t ≠ k v₁ := fun h => one_ne_zero ((hbt.symm.trans (congrArg b (hk h))).trans hb1)
      omega
    exact ⟨Or.inr ⟨hdt,hb0,hb1,t,hkt,by simp [hbt]⟩,
      positive_slot_degree k hk b t (by omega) (by simp [hbt])⟩

end Turan.SectionTwo
