module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.MehlerJetsRoots
public import Turan.Hermite

@[expose] public section
open Polynomial
noncomputable section
namespace Turan.MehlerJets

theorem cubic_trinomial_root_triple (a : ℂ) (ha : a ≠ 0) :
    let G := 1 + 2*X + C a * Giroux.mode 3
    ∃ ζ : Fin 3 → ℂ, (List.ofFn ζ : Multiset ℂ) = G.roots ∧
      (∑ i, (ζ i).im)=0 ∧ (∏ i, ‖ζ i-(-1/2:ℂ)‖)=5/8 ∧
      ∃ i, |(ζ i).re| ≤ 2 ∧ |(ζ i).im| < 76/100 := by
  classical
  let d := a*(Giroux.scale 3:ℂ)⁻¹
  have hd : d ≠ 0 := mul_ne_zero ha (inv_ne_zero (Complex.ofReal_ne_zero.mpr (Giroux.scale_pos 3).ne'))
  let G : Polynomial ℂ := 1+2*X+C a*Giroux.mode 3
  change ∃ ζ : Fin 3 → ℂ, (List.ofFn ζ : Multiset ℂ) = G.roots ∧ _
  have hG : G = family 2 3 0 d := by simp [G,family,Giroux.mode,d,mul_assoc]
  have hg : G.natDegree=3 := by rw [hG,family_degree 2 3 (by decide) (by decide)]; simp [hd]
  obtain ⟨x,y,v,hr⟩ := Multiset.card_eq_three.mp ((IsAlgClosed.splits G).natDegree_eq_card_roots.symm.trans hg)
  let ζ : Fin 3 → ℂ := ![x,y,v]
  have hroots : (List.ofFn ζ : Multiset ℂ) = G.roots := by rw [hr]; rfl
  have hcoeff : G.nextCoeff=0 := by
    rw [nextCoeff_of_natDegree_pos (by omega),hg]
    change G.coeff 2 = 0
    rw [hG]
    simp [family,hermite_low.2,mul_sub,sub_mul,coeff_add,coeff_sub,coeff_C_mul,
      coeff_X_pow, coeff_mul_X, coeff_one, mul_assoc, ← C_ofNat]
  have hsum := (IsAlgClosed.splits G).nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [hcoeff] at hsum
  have hne : G ≠ 0 := by intro h; simp [h] at hg
  have hs := (mul_eq_zero.mp hsum.symm).resolve_left (neg_ne_zero.mpr (leadingCoeff_ne_zero.mpr hne))
  have hs' : (∑ i, (ζ i).im)=0 := by
    rw [hr] at hs
    simpa [ζ,Fin.sum_univ_three,Complex.add_im,add_assoc] using congrArg Complex.im hs
  have hp := trinomial_distance_product 3 (by decide) a ha
  change (G.roots.map _).prod = _ at hp
  rw [hr,hermite_low.2] at hp
  have hp' : (∏ i, ‖ζ i-(-1/2:ℂ)‖) = 5/8 := by
    norm_num [eval_sub,eval_mul,eval_pow, Multiset.map_cons,Multiset.prod_cons] at hp
    simpa [ζ,Fin.prod_univ_three,mul_assoc,mul_comm,mul_left_comm,neg_div,sub_neg_eq_add,one_div] using hp
  refine ⟨ζ,hroots,hs',hp',?_⟩
  by_contra! hfail
  have lower (i) : 76/100 ≤ ‖ζ i-(-1/2:ℂ)‖ := by
    by_cases he : |(ζ i).re| ≤ 2
    · exact (hfail i he).trans (by simpa using Complex.abs_im_le_norm (ζ i-(-1/2:ℂ)))
    · have h := Complex.abs_re_le_norm (ζ i-(-1/2:ℂ))
      simp only [Complex.sub_re,Complex.neg_re,Complex.div_ofNat_re,Complex.one_re] at h
      have hh := abs_add_le ((ζ i).re-(-1/2)) (-1/2)
      rw [sub_add_cancel] at hh
      rw [abs_of_neg (by norm_num : (-1/2:ℝ)<0)] at hh
      linarith
  have inside (i) : |(ζ i).re| ≤ 2 := by
    by_contra! hh
    have ht := abs_add_le ((ζ i).re-(-1/2)) (-1/2)
    rw [sub_add_cancel,abs_of_neg (by norm_num : (-1/2:ℝ)<0)] at ht
    have h : |(ζ i).re-(-1/2)| ≤ ‖ζ i-(-1/2:ℂ)‖ := by
      simpa only [Complex.sub_re, Complex.div_ofNat_re,Complex.neg_re,Complex.one_re] using
        Complex.abs_re_le_norm (ζ i-(-1/2:ℂ))
    have hl : 3/2 ≤ ‖ζ i-(-1/2:ℂ)‖ := by linarith
    let B (j : Fin 3) : ℝ := if j=i then 3/2 else 76/100
    have hb := Finset.prod_le_prod₀ (s := Finset.univ) (f := B)
      (g := fun j => ‖ζ j-(-1/2:ℂ)‖) (fun j _ => by dsimp [B]; split <;> norm_num)
      (fun j _ => by
        by_cases he : j=i
        · subst j; simpa [B] using hl
        · simpa [B,he] using lower j)
    rw [hp'] at hb
    fin_cases i <;> norm_num [Fin.prod_univ_three,B] at hb
  obtain ⟨_,hle,hgt⟩ := cubic_large_imaginary_factor ζ hs' (fun i => hfail i (inside i))
  exact hgt.not_ge (hle.trans_eq hp')

theorem g1_chart_count_given (G1 : TrinomialDiskCheck) (n : ℕ) (hn : 4 ≤ n) (hn' : n ≤ 79)
    (swap : Bool) (θ : ℂ) (hx : |θ.re| ≤ 1) (hy : 0 ≤ θ.im) (hy' : θ.im ≤ 1) :
    ∃ (x y : ℤ) (t k : ℕ), t ∈ ([4,6,8,12,16,24,32] : List ℕ) ∧ 1 ≤ k ∧ k ≤ 4 ∧
      let w : ℂ := ⟨(x:ℝ)/16384,(y:ℝ)/16384⟩
      let r := (t:ℝ)/(16*chartScale n)
      let G := trinomialChart n swap θ
      0 < r ∧ ‖w‖+r < 9/10 ∧ |w.im|+r < 76/100 ∧
      (G.roots.filter (fun z => ‖z-w‖ < r)).card = k ∧
      ∀ z ∈ G.roots, ‖z-w‖ < r → |z.re| ≤ 2 ∧ |z.im| < 76/100 := by
  obtain ⟨x,y,t,k,ht,hk,hk',hsize,hheight,hdom⟩ := G1 n hn hn' swap θ hx hy hy'
  have htp : 0 < t := by simp at ht; omega
  have hN : 0 < chartScale n := by unfold chartScale; omega
  let w : ℂ := ⟨(x:ℝ)/16384,(y:ℝ)/16384⟩
  let r : ℝ := (t:ℝ)/(16*chartScale n)
  have hr : 0 < r := by dsimp [r]; positivity
  exact ⟨x,y,t,k,ht,hk,hk',hr,hsize,hheight,g1_original_disk_count n swap θ w r k
    hr hk hsize hheight hdom⟩

end Turan.MehlerJets
