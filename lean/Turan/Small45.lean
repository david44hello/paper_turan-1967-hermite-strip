-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.Degree
import Turan.Small45Nodes
import Turan.Small45Bound

open Polynomial
namespace Turan

/-- Appendix A.3, the (4,5) row. -/
theorem lemma_twenty_one (a b : ℂ) : ∃ z : ℂ, (family 4 5 a b).eval z = 0 ∧ |z.im| < 17/20 := by
  by_contra! hall
  let p := family 4 5 a b
  obtain ⟨l,r,hl₀,hl₁,hr₀,hr₁,h₁⟩ := Small45.nodes_one
  obtain ⟨u,v,hu₀,hu₁,hv₀,hv₁,h₂⟩ := Small45.nodes_two
  have nonzero (s : ℝ) : p.eval ((s:ℂ)-1/2) ≠ 0 := by
    intro hz
    have hbad := hall _ hz
    norm_num at hbad
  let R (s t : ℝ) (z : ℂ) := ‖(z+1/2)-(s:ℂ)‖ / ‖(z+1/2)-(t:ℂ)‖
  let K (z : ℂ) := (R l r z)^2*R u v z
  have hprod : (p.roots.map K).prod = (|l|/|r|)^2*(|u|/|v|) := by
    dsimp only [K]
    rw [Multiset.prod_map_mul,Multiset.prod_map_pow]
    exact congrArg₂ (· * ·) (congrArg (· ^ 2) (shifted_node_product p l r (h₁ a b) hr₁.ne (nonzero r)))
      (shifted_node_product p u v (h₂ a b) (by linarith) (nonzero v))
  have hlarge₁ : 20*125000 < |l|/|r| := by
    rw [abs_of_neg (by linarith : l < 0), abs_of_neg hr₁]
    apply (lt_div_iff₀ (by linarith : 0 < -r)).mpr
    linarith only [hl₁,hr₀]
  have hlarge₂ : 1/6 < |u|/|v| := by
    rw [abs_of_pos (by linarith : 0 < u), abs_of_pos (by linarith : 0 < v)]
    apply (lt_div_iff₀ (by linarith : 0 < v)).mpr
    linarith only [hu₀,hv₁]
  have hlarge : (240:ℝ)^5 < (p.roots.map K).prod := by
    rw [hprod]
    calc
      (240:ℝ)^5 < (20*125000)^2*(1/6) := by norm_num
      _ ≤ _ := by gcongr
  have hcard : p.roots.card ≤ 5 := by
    apply p.card_roots'.trans
    dsimp only [p]
    rw [family_degree 4 5 (by decide) (by decide)]
    split_ifs <;> decide
  have hbound (z : ℂ) (hz : z ∈ p.roots) : K z ≤ 240 := by
    have hw : 17/20 ≤ |(z+1/2).im| := by simpa using hall z (Polynomial.isRoot_of_mem_roots hz)
    exact (Small45.factor_bound (z+1/2) hw l r u v
      ⟨hl₀,hl₁⟩ ⟨hr₀,hr₁⟩ ⟨hu₀,hu₁⟩ ⟨hv₀,hv₁⟩).le
  have hup := Multiset.prod_map_le_prod_map₀ K (fun _ => (240:ℝ))
    (s := p.roots) (fun z _ => by dsimp [K,R]; positivity) hbound
  simp only [Multiset.map_const',Multiset.prod_replicate] at hup
  exact hlarge.not_ge (hup.trans (pow_le_pow_right₀ (by norm_num) hcard))

#print axioms lemma_twenty_one

end Turan
