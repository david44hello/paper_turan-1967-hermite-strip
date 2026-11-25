-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.DiskNodes

noncomputable section
namespace Turan

/-- On a fixed inner disk, the high Hermite mode is uniformly small relative
to a zero-free four-slot polynomial once its upper degree is sufficiently large. -/
theorem slot_suppression (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ R : ℝ, K < R ∧ ∃ M : ℕ, ∀ n m : ℕ, 2 ≤ n → n < m → M ≤ m → ∀ c d a b : ℂ,
      (∀ w : ℂ, ‖w‖ ≤ R → (fourSlots n m c d a b).eval w ≠ 0) →
      ∀ z : ℂ, ‖z‖ ≤ K → ‖b*(hermite m).eval z / (fourSlots n m c d a b).eval z‖ < ε := by
  let S := 2*(K+1)+1
  obtain ⟨C, hC, hproj⟩ := fourSlots_projection_bound S (by dsimp [S]; linarith)
  obtain ⟨M, hM⟩ := disk_suppression_threshold K ε C hK hε hC
  refine ⟨S+2, by dsimp [S]; linarith, M, ?_⟩
  intro n m hn hnm hm c d a b hfree
  exact hM m hm (fourSlots n m c d a b) b
    (fun w hw => hfree w (hw.trans (by dsimp [S]; linarith)))
    (fun w hw => hproj n m hn hnm c d a b w hfree hw.le)

end Turan
