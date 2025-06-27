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

open Matrix

structure ConvIter (ι 𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Fintype ι] [DecidableEq ι] where
  A : Matrix ι ι 𝕜
  M : Matrix ι ι 𝕜
  N : Matrix ι ι 𝕜 := A - M
  b : ι → 𝕜
  eq   : A = M + N := by simp
  inv  : Invertible M
  spec : ‖(-M⁻¹ * N).toLin'.toContinuousLinearMap‖₊ < 1

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def ConvIter.toFun (self : ConvIter ι 𝕜) (v: ι → 𝕜) := (- self.M⁻¹ * self.N) *ᵥ v + self.M⁻¹ *ᵥ self.b

theorem iter_contracting (it : ConvIter ι 𝕜) :
    ContractingWith ‖(-it.M⁻¹ * it.N).toLin'.toContinuousLinearMap‖₊ it.toFun := by
  have hl : LipschitzWith ‖(-it.M⁻¹ * it.N).toLin'.toContinuousLinearMap‖₊ it.toFun := by
    dsimp [LipschitzWith, ConvIter.toFun]
    intro v w
    rw [edist_add_right]
    apply ContinuousLinearMap.lipschitz
  exact ⟨it.spec, hl⟩

theorem iter_conv (it : ConvIter ι 𝕜) (v : ι → 𝕜):
    ∃ x : ι → 𝕜, Filter.Tendsto (fun n => it.toFun^[n] v) Filter.atTop (nhds x) := by
  let ⟨x, _, hr, _⟩ := ContractingWith.exists_fixedPoint (iter_contracting it) v (edist_ne_top v (it.toFun v))
  exact ⟨x, hr⟩

theorem solution_is_fixpt (it : ConvIter ι 𝕜) (x : ι → 𝕜) (heq: it.A *ᵥ x = it.b):
    Function.IsFixedPt it.toFun x := by
  let inv := it.inv
  rw [it.eq, add_mulVec] at heq
  apply eq_sub_of_add_eq at heq
  apply congr_arg (it.M⁻¹ *ᵥ ·) at heq
  rw [mulVec_mulVec, inv_mul_of_invertible, one_mulVec, mulVec_sub, mulVec_mulVec] at heq
  simp [Function.IsFixedPt]
  rw [sub_eq_add_neg, ←neg_mulVec] at heq
  simp only [ConvIter.toFun, neg_mul]
  rw [add_comm, ←heq]

theorem iter_tendsto_solution (it : ConvIter ι 𝕜) (v x : ι → 𝕜) (h: it.A *ᵥ x = it.b):
    Filter.Tendsto (fun n ↦ it.toFun^[n] v) Filter.atTop (nhds x) := by
  let ⟨x', hic⟩ := iter_conv it v
  have : Filter.Tendsto (fun (n:Nat) => x) Filter.atTop (nhds x) := tendsto_const_nhds
  have hfe: (fun n => it.toFun^[n] x) = (fun n => x) := by
    funext n
    exact Function.iterate_fixed (sol_is_fixpt it x h) n
  rw [←hfe] at this
  have hf : ContractingWith ‖(-it.M⁻¹ * it.N).toLin'.toContinuousLinearMap‖₊ it.toFun :=
    iter_contracting it
  let hxfp := ContractingWith.tendsto_iterate_fixedPoint hf v
  rw [←ContractingWith.fixedPoint_unique hf (sol_is_fixpt it x h)] at hxfp
  assumption

def diag_dominant (M : Matrix ι ι 𝕜) :=
  ∀ i : ι, (∑ j ∈ Finset.univ.erase i, ‖M i j‖₊) < ‖M i i‖₊

variable (M : Matrix ι ι 𝕜) (b : ι → 𝕜) [LE 𝕜] [OrderBot 𝕜] [NormedAlgebra ℝ 𝕜]

noncomputable instance : NormedAddCommGroup (Matrix ι ι 𝕜) := Matrix.linftyOpNormedAddCommGroup
instance : NormedSpace 𝕜 (Matrix ι ι 𝕜) := Matrix.linftyOpNormedSpace

noncomputable def jacobi (hd : diag_dominant M) : ConvIter ι 𝕜 := by
  have hnz : ∀ i ∈ Finset.univ, M.diag i ≠ 0 := by
    intro i _
    by_contra! h
    simp at *
    dsimp [diag_dominant] at *
    specialize hd i
    simp [h] at hd
  haveI : Invertible (diagonal M.diag) := by
    apply invertibleOfIsUnitDet
    rw [det_diagonal]
    apply isUnit_iff_ne_zero.mpr
    rw [Finset.prod_ne_zero_iff]
    exact hnz
  exact {
    A := M
    M := (diagonal M.diag)
    b := b
    inv := by infer_instance
    spec := by
      rw [← linfty_opNNNorm_toMatrix, LinearMap.coe_toContinuousLinearMap, LinearMap.toMatrix'_toLin']
      rw [Matrix.linfty_opNNNorm_def, Finset.sup_lt_iff (by simp)]
      intro i _
      have h : M - diagonal M.diag = of fun i j => if i = j then 0 else M i j := by
        funext i j
        by_cases h : i = j <;> simp [sub_apply, h]
      let f := fun j => ‖((diagonal M.diag)⁻¹ * (of fun i j => if i = j then 0 else M i j)) i j‖₊
      calc ∑ j, ‖(-(diagonal M.diag)⁻¹ * (M - diagonal M.diag)) i j‖₊ = _ := by rfl
        _ = ∑ j, ‖(-(diagonal M.diag)⁻¹ * (of fun i j => if i = j then 0 else M i j)) i j‖₊ := by rw [h]
        _ = ∑ j, ‖((diagonal M.diag)⁻¹ * (of fun i j => if i = j then 0 else M i j)) i j‖₊ := by simp
        _ = ∑ j, f j := by simp [f]
        _ = ∑ j, f j - f i := by simp [f, inv_diagonal, diagonal_mul, of_apply]
        _ = ∑ j ∈ Finset.univ.erase i, f j := by simp [←Finset.sum_erase_add (s := Finset.univ) (a := i)]
        _ = ∑ j ∈ Finset.univ.erase i, ‖(M i i)⁻¹ * M i j‖₊ := by
          dsimp [f]
          apply Finset.sum_congr (by rfl)
          intro j hj
          rw [inv_diagonal, diagonal_mul, of_apply]
          rw [if_neg (Finset.ne_of_mem_erase hj).symm]
          have hu : IsUnit M.diag := by
            refine isUnit_diagonal.mp ?_
            exact isUnit_of_invertible (diagonal M.diag)
          rw [Ring.inverse_of_isUnit hu]
          simp
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

variable [LinearOrder ι] [DecidableLT ι] [LocallyFiniteOrderBot ι] [LocallyFiniteOrderTop ι]

def p (i : ι) : ℝ :=
    (∑ j : Finset.Iio i, ‖(M i j)/(M i i)‖ * p j) + ∑ j ∈ { j > i | j ∈ Finset.univ }, ‖(M i j)/(M i i)‖
  termination_by (Finset.Iio i).card
  decreasing_by
    apply Finset.card_lt_card
    apply Finset.Iio_ssubset_Iio
    exact Finset.mem_Iio.mp j.prop

noncomputable def gauss_seidel (h : ∀ i : ι, (p M i) < 1) (hnz : ∀ i : ι, M i i ≠ 0) : ConvIter ι 𝕜 := {
  A := M
  M := of fun i j => if i ≤ j then M i j else 0
  b := b
  inv := by
    apply invertibleOfIsUnitDet
    rw [det_of_upperTriangular]
    · apply isUnit_iff_ne_zero.mpr
      rw [Finset.prod_ne_zero_iff]
      intro i _
      simp [of_apply]
      exact hnz i
    · intro i j hij
      simp [of_apply]
      intro hle
      exfalso
      exact not_le.mpr hij hle
  spec := by
    sorry
}
