module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Turan.TailNodesGeometry
public import Turan.TailNodesProduct
public import Turan.TailHyperbolic

@[expose] public section

namespace Turan

theorem lemma_seventeen (j : ℕ) (hj : 225 ≤ j) :
    psi j (-1/2) = 0 ∨
      -Real.log (nodeProduct j) > (608/1000)*Real.sqrt (2*(j:ℝ)-1125/100) - 315/1000 := by
  by_cases h0 : psi j (-1/2) = 0
  · exact Or.inl h0
  obtain ⟨d, e, hd, he, hp⟩ := tail_node_pairs j hj h0
  apply Or.inr
  exact (tail_paired_log_bound j hj _ rfl _ rfl d e (fun i => (hp i).1)
    (fun i => (hp i).2.1) (fun i => (hp i).2.2.2.2)).trans_le
    (tail_node_pair_sum_le j _ h0 d e hd he (fun i =>
      ⟨(hp i).1, (hp i).2.1, (hp i).2.2.1, (hp i).2.2.2.1⟩))

end Turan
