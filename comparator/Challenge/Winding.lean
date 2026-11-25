-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.WindingDefs
namespace Turan
theorem polygon_forces_zero (p : Polynomial ℂ) (h : ℝ) (check : PolygonCheck p h) :
    ∃ z : ℂ, p.eval z = 0 ∧ |z.im| < h := by sorry

theorem winding_certificate_gap (n m : ℕ) (hn : 2 ≤ n) (hnm : n < m)
    (check : WindingCertificate n m) (a b : ℂ) :
    ∃ z : ℂ, (family n m a b).eval z = 0 ∧ |z.im| < 87/100 := by sorry
end Turan
