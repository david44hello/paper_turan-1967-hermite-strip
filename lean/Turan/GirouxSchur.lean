-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Turan.ScaledFamily
import Turan.Degree
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Tactic

noncomputable section
open Polynomial Module Matrix
open scoped InnerProductSpace ComplexConjugate
namespace Turan.Giroux

/-- Schur's diagonal, with multiplicity. Split off an eigenspace and compress to
its orthogonal complement, where the same argument applies in smaller dimension. -/
private theorem schur (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) :
    ∃ (ι : Type) (_ : Fintype ι) (b : OrthonormalBasis ι ℂ E),
      T.charpoly = ∏ i, (X - C (inner ℂ (b i) (T (b i)))) := by
  classical
  generalize hdim : finrank ℂ E = n
  induction n using Nat.strong_induction_on generalizing E with
  | h n ih =>
    by_cases hn : n = 0
    · let b := stdOrthonormalBasis ℂ E
      have : IsEmpty (Fin (finrank ℂ E)) := by rw [hdim, hn]; infer_instance
      exact ⟨_, inferInstance, b, by rw [← T.charpoly_toMatrix b.toBasis]; simp [Matrix.charpoly_isEmpty]⟩
    have : Nontrivial E := (finrank_pos_iff (R := ℂ)).mp (by omega)
    obtain ⟨μ, hμ⟩ := End.exists_eigenvalue T
    let K := End.eigenspace T μ
    let D := Kᗮ
    have hK : 0 < finrank ℂ K := finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hμ)
    have hdimD : finrank ℂ D < n := by have := K.finrank_add_finrank_orthogonal; dsimp [D]; omega
    let U := D.orthogonalProjectionOnto.toLinearMap ∘ₗ T ∘ₗ D.subtype
    obtain ⟨ι, fi, v, hv⟩ := ih _ hdimD D U rfl
    let u := stdOrthonormalBasis ℂ K
    let e := K.prodEquivOfIsCompl D K.isCompl_orthogonal
    let B := (u.toBasis.prod v.toBasis).map e
    have hl (i) : B (.inl i) = (u i : E) := by
      simp [B, e]
    have hr (i) : B (.inr i) = (v i : E) := by
      simp [B, e]
    have horth (i j) : inner ℂ (u i : E) (v j : E) = 0 := (v j).property _ (u i).property
    have hB : Orthonormal ℂ B := by
      rw [orthonormal_iff_ite]
      rintro (i|i) (j|j)
      · simpa [hl] using (orthonormal_iff_ite.mp u.orthonormal i j)
      · simp [hl, hr, horth]
      · simp [hl, hr, inner_eq_zero_symm.mpr (horth j i)]
      · simpa [hr] using (orthonormal_iff_ite.mp v.orthonormal i j)
    let b := B.toOrthonormalBasis hB
    have heig (i) : T (u i : E) = μ • (u i : E) := End.mem_eigenspace_iff.mp (u i).property
    have hentry (i j) : LinearMap.toMatrix b.toBasis b.toBasis T i j = inner ℂ (B i) (T (B j)) := by
      rw [LinearMap.toMatrix_apply]
      change b.repr (T (b j)) i = _
      rw [OrthonormalBasis.repr_apply_apply]
      simp [b]
    have hcomp (i j) : inner ℂ (v i) (U (v j)) = inner ℂ (v i : E) (T (v j : E)) :=
      D.inner_orthogonalProjectionOnto_eq_of_mem_left _ _
    have hblock : LinearMap.toMatrix b.toBasis b.toBasis T = Matrix.fromBlocks
        (Matrix.diagonal (fun _ => μ)) (Matrix.of fun i j => inner ℂ (u i : E) (T (v j : E)))
        0 (LinearMap.toMatrix v.toBasis v.toBasis U) := by
      ext (i|i) (j|j) <;> rw [hentry]
      · simp [hl, heig, inner_smul_right, ← K.coe_inner, u.inner_eq_ite, Matrix.diagonal_apply]
      · simp [hl, hr]
      · simp [hr, hl, heig, inner_smul_right, inner_eq_zero_symm.mpr (horth j i)]
      · simp [hr, LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply, hcomp]
    refine ⟨_, inferInstance, b, ?_⟩
    rw [← T.charpoly_toMatrix b.toBasis, hblock, Matrix.charpoly_fromBlocks_zero₂₁,
      Matrix.charpoly_diagonal, U.charpoly_toMatrix, hv, Fintype.prod_sum_type]
    have hu (i) : ‖(u i : E)‖ = 1 := u.orthonormal.1 i
    simp [b, hl, hr, heig, inner_smul_right, hcomp, hu]

end Turan.Giroux

namespace Turan.Giroux

/-- A Hermitian operator perturbed by a single outer product. -/
theorem rank_one_root_sum (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (J : E →ₗ[ℂ] E) (hJ : J.IsSymmetric) (u v : E) :
    ((J - (InnerProductSpace.rankOne ℂ u v).toLinearMap).charpoly.roots.map
      (fun z : ℂ => |z.im|)).sum ≤ ‖u‖ * ‖v‖ := by
  classical
  let T := J - (InnerProductSpace.rankOne ℂ u v).toLinearMap
  obtain ⟨ι, fi, b, hb⟩ := schur E T
  let f (i : ι) := inner ℂ (b i) (T (b i))
  have hr : T.charpoly.roots = Finset.univ.val.map f := by
    rw [hb]
    convert roots_multiset_prod_X_sub_C (Finset.univ.val.map f) using 2
    simp only [Finset.prod, Multiset.map_map, Function.comp_def, f]
  change (T.charpoly.roots.map _).sum ≤ _
  rw [hr, Multiset.map_map]
  change ∑ i, |(f i).im| ≤ _
  calc
    _ ≤ ∑ i, ‖inner ℂ (b i) u‖ * ‖inner ℂ v (b i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hj : (inner ℂ (b i) (J (b i))).im = 0 := hJ.im_inner_self_apply _
      simp only [f, T, LinearMap.sub_apply, ContinuousLinearMap.coe_coe,
        InnerProductSpace.rankOne_apply, inner_sub_right, inner_smul_right,
        Complex.sub_im, hj, zero_sub, abs_neg]
      simpa [norm_mul, mul_comm] using
        Complex.abs_im_le_norm (inner ℂ v (b i) * inner ℂ (b i) u)
    _ ≤ _ := by
      simpa [b.sum_sq_norm_inner_left, b.sum_sq_norm_inner_right, Real.sqrt_sq (norm_nonneg _)]
        using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖inner ℂ (b i) u‖)
          (fun i => ‖inner ℂ v (b i)‖)

end Turan.Giroux
