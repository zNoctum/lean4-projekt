import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.NNNorm
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Group.Invertible.Basic
import Lean4Projekt.Iter

open Matrix

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def diag_dominant (M : Matrix ι ι 𝕜) :=
  ∀ i : ι, (∑ j ∈ Finset.univ.erase i, ‖M i j‖₊) < ‖M i i‖₊

variable (M : Matrix ι ι 𝕜) (b : ι → 𝕜)

variable [LE 𝕜] [OrderBot 𝕜] [NormedAlgebra ℝ 𝕜]

noncomputable instance : NormedAddCommGroup (Matrix ι ι 𝕜) := Matrix.linftyOpNormedAddCommGroup
instance : NormedSpace 𝕜 (Matrix ι ι 𝕜) := Matrix.linftyOpNormedSpace

noncomputable def jacobi (hd : diag_dominant M) : ConvIter ι 𝕜 := by
  /- Proof that `diag_dominant M` implies a nonzero diagonal-/
  have hnz : ∀ i ∈ Finset.univ, M.diag i ≠ 0 := by
    intro i _
    by_contra! h
    simp [diag_dominant] at *
    specialize hd i
    simp [h] at hd
  /- Proof that a -/
  haveI : Invertible (diagonal M.diag) := by
    apply invertibleOfIsUnitDet
    rw [det_diagonal]
    apply isUnit_iff_ne_zero.mpr
    rw [Finset.prod_ne_zero_iff]
    exact hnz
  exact {
    A := M
    M := diagonal M.diag
    b := b
    inv := by infer_instance
    spec := by
      -- Apply the definition of the L_infinity norm.
      rw [← linfty_opNNNorm_toMatrix, LinearMap.coe_toContinuousLinearMap, LinearMap.toMatrix'_toLin']
      rw [linfty_opNNNorm_def, Finset.sup_lt_iff (by norm_num)]
      -- prove the rest for each dimension separatly
      intro i _
      have h : M - diagonal M.diag = of fun i j => if i = j then 0 else M i j := by
        funext i j
        by_cases h : i = j <;> simp [sub_apply, h]
      let f := fun j => ‖((diagonal M.diag)⁻¹ * (of fun i j => if i = j then 0 else M i j)) i j‖₊
      calc ∑ j, ‖(-(diagonal M.diag)⁻¹ * (M - diagonal M.diag)) i j‖₊ = _ := by rfl
        _ = ∑ j, f j := by
          simp [h, f]
        _ = ∑ j, f j - f i := by
          simp [f, inv_diagonal, diagonal_mul, of_apply]
        _ = ∑ j ∈ Finset.univ.erase i, f j := by
          simp [←Finset.sum_erase_add (s := Finset.univ) (a := i)]
        _ = ∑ j ∈ Finset.univ.erase i, ‖(M i i)⁻¹ * M i j‖₊ := by
          dsimp [f]
          apply Finset.sum_congr (by rfl)
          intro j hj
          rw [inv_diagonal, diagonal_mul, of_apply]
          rw [if_neg (Finset.ne_of_mem_erase hj).symm]
          have hu : IsUnit M.diag := by
            refine isUnit_diagonal.mp ?_
            exact isUnit_of_invertible (diagonal M.diag)
          simp [Ring.inverse_of_isUnit hu]
        _ = ∑ j ∈ Finset.univ.erase i, ‖M i i‖₊⁻¹ * ‖M i j‖₊ := by simp
        _ = (∑ j ∈ Finset.univ.erase i, ‖M i j‖₊) * ‖M i i‖₊⁻¹ := by
          rw [Finset.sum_mul (Finset.univ.erase i)]
          apply Finset.sum_congr (by rfl)
          intro _ _
          rw [mul_comm]
      rw [←NNReal.lt_inv_iff_mul_lt]
      · simpa using (hd i)
      · apply inv_ne_zero
        rw [←diag_apply M, nnnorm_ne_zero_iff]
        exact hnz i (Finset.mem_univ i)
  }
