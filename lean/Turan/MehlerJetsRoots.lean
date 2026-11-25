-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Degree
import Turan.GirouxJacobi
import Turan.Rouche
import Turan.TransferDefs
import Turan.TrinomialDefs

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace Turan.MehlerJets

theorem trinomial_distance_product (n : ℕ) (hn : 2 ≤ n) (a : ℂ) (ha : a ≠ 0) :
    let G : Polynomial ℂ := 1 + 2*X + C a * Giroux.mode n
    (G.roots.map (fun ζ : ℂ => ‖ζ-(-1/2 : ℂ)‖)).prod =
      ‖(hermite n).eval (-1/2)‖ / (2:ℝ)^n := by
  intro G
  let d := a*(Giroux.scale n : ℂ)⁻¹
  have hd : d ≠ 0 := mul_ne_zero ha (inv_ne_zero (Complex.ofReal_ne_zero.mpr (Giroux.scale_pos n).ne'))
  have hG : G = 1+2*X+C d*hermite n := by simp [G,Giroux.mode,d,mul_assoc]
  have hdeg : (1+2*X : Polynomial ℂ).natDegree < (C d * hermite n).natDegree := by
    rw [natDegree_C_mul hd, (hermite_degree n).1]
    have h : (1+2*X : Polynomial ℂ).natDegree = 1 := by simp
    omega
  have hl : G.leadingCoeff = d*2^n := by
    rw [hG, leadingCoeff_add_of_degree_lt (degree_lt_degree hdeg), leadingCoeff_mul,
      leadingCoeff_C, (hermite_degree n).2]
  let w : ℂ := -1/2
  have hv : G.eval w = d*(hermite n).eval w := by rw [hG]; norm_num [w,eval_add,eval_mul]
  have hp := congrArg norm ((IsAlgClosed.splits G).eval_eq_prod_roots w)
  rw [hv, hl, norm_mul d ((hermite n).eval w), norm_mul (d*2^n), norm_mul d (2^n), norm_pow, Complex.norm_ofNat,
    Multiset.norm_prod, Multiset.map_map] at hp
  have hdist : (fun x : ℂ => ‖x-w‖) = (norm ∘ (w-·)) := funext (fun x => norm_sub_rev x w)
  change (G.roots.map (fun ζ : ℂ => ‖ζ-w‖)).prod = ‖(hermite n).eval w‖ / 2^n
  rw [hdist, eq_div_iff (by positivity)]
  apply mul_left_cancel₀ (norm_ne_zero_iff.mpr hd)
  linear_combination -hp

theorem cubic_large_imaginary_factor (ζ : Fin 3 → ℂ)
    (hsum : (∑ i, (ζ i).im) = 0) (him : ∀ i, 76/100 ≤ |(ζ i).im|) :
    (∃ i, 152/100 ≤ |(ζ i).im|) ∧
    (76/100:ℝ)^2*(152/100) ≤ ∏ i, ‖ζ i - (-1/2:ℂ)‖ ∧
    (5/8:ℝ) < (76/100:ℝ)^2*(152/100) := by
  rw [Fin.sum_univ_three] at hsum
  have hw : ∃ i, 152/100 ≤ |(ζ i).im| := by
    by_contra! h
    obtain ⟨h0,h0'⟩ := abs_lt.mp (h 0)
    obtain ⟨h1,h1'⟩ := abs_lt.mp (h 1)
    obtain ⟨h2,h2'⟩ := abs_lt.mp (h 2)
    rcases le_abs.mp (him 0) with he | he <;>
      rcases le_abs.mp (him 1) with hf | hf <;>
      rcases le_abs.mp (him 2) with hg | hg <;> linarith
  have hnorm (i) : |(ζ i).im| ≤ ‖ζ i-(-1/2:ℂ)‖ := by
    simpa using Complex.abs_im_le_norm (ζ i-(-1/2:ℂ))
  refine ⟨hw, ?_, by norm_num⟩
  obtain ⟨i,hi⟩ := hw
  let b (j : Fin 3) : ℝ := if j = i then 152/100 else 76/100
  have hprod : (∏ j, b j) ≤ ∏ j, ‖ζ j-(-1/2:ℂ)‖ := by
    apply Finset.prod_le_prod₀ (fun j _ => by dsimp [b]; split <;> norm_num)
    intro j _
    by_cases h : j=i
    · subst j; simpa [b] using hi.trans (hnorm i)
    · simpa [b,h] using (him j).trans (hnorm j)
  convert hprod using 1
  fin_cases i <;> norm_num [b,Fin.prod_univ_three]

theorem g1_original_disk_count (n : ℕ) (swap : Bool) (θ ω : ℂ) (ρ : ℝ) (k : ℕ)
    (hρ : 0 < ρ) (hk : 1 ≤ k) (hsize : ‖ω‖+ρ < 9/10) (hheight : |ω.im|+ρ < 76/100)
    (hdom : let p := diskExpansion (trinomialChart n swap θ) ω ρ
      (∑ j ∈ p.support.erase k, ‖p.coeff j‖) < ‖p.coeff k‖) :
    let G := trinomialChart n swap θ
    (G.roots.filter (fun z => ‖z-ω‖ < ρ)).card = k ∧
    ∀ z ∈ G.roots, ‖z-ω‖ < ρ → |z.re| ≤ 2 ∧ |z.im| < 76/100 := by
  classical
  intro G
  let p := diskExpansion G ω ρ
  have hp : (p.roots.filter (fun v => ‖v‖ < 1)).card = k :=
    dominant_polynomial_term p k hk hdom
  have ha : p.roots.map (fun v : ℂ => (ρ:ℂ)*v+ω) = G.roots := by
    simpa only [p,diskExpansion,add_comm (C ω)] using
      G.map_roots_comp_C_mul_X_add_C (ρ:ℂ) ω (Complex.ofReal_ne_zero.mpr hρ.ne').isUnit
  constructor
  · rw [← ha, Multiset.filter_map, Multiset.card_map]
    convert hp using 2
    ext v
    simp [abs_of_pos hρ, mul_lt_iff_lt_one_right hρ]
  · intro z _ hz
    have h := norm_add_le (z-ω) ω
    rw [sub_add_cancel] at h
    have him := Complex.abs_im_le_norm (z-ω)
    rw [Complex.sub_im] at him
    have hzi := abs_add_le (z.im-ω.im) ω.im
    rw [sub_add_cancel] at hzi
    exact ⟨by linarith [Complex.abs_re_le_norm z], by linarith⟩

end Turan.MehlerJets
