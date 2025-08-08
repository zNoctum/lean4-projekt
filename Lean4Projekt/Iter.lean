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
  /-- The inital Matrix of the expression `Ax = b` -/
  A : Matrix ι ι 𝕜
  /-- -/
  M : Matrix ι ι 𝕜
  N : Matrix ι ι 𝕜 := A - M
  /-- The result vector in `Ax = b` -/
  b : ι → 𝕜
  eq   : A = M + N := by simp
  inv  : Invertible M
  spec : ‖(-M⁻¹ * N).toLin'.toContinuousLinearMap‖₊ < 1

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Definition of the actual iteration function -/
noncomputable def ConvIter.toFun (self : ConvIter ι 𝕜) (v: ι → 𝕜) := (- self.M⁻¹ * self.N) *ᵥ v + self.M⁻¹ *ᵥ self.b

lemma iter_contracting (it : ConvIter ι 𝕜) :
    ContractingWith ‖(-it.M⁻¹ * it.N).toLin'.toContinuousLinearMap‖₊ it.toFun := by
  have hl : LipschitzWith ‖(-it.M⁻¹ * it.N).toLin'.toContinuousLinearMap‖₊ it.toFun := by
    -- simplify the involved definitions
    dsimp [LipschitzWith, ConvIter.toFun]
    intro v w
    rw [edist_add_right]
    apply ContinuousLinearMap.lipschitz
  exact ⟨it.spec, hl⟩

/- Wrapper lemma over the banach fixpoint theorem for ConvIters -/
lemma iter_conv (it : ConvIter ι 𝕜) (v : ι → 𝕜):
    ∃ x : ι → 𝕜, Filter.Tendsto (fun n => it.toFun^[n] v) Filter.atTop (nhds x) := by
  let ⟨x, _, hr, _⟩ := ContractingWith.exists_fixedPoint (iter_contracting it) v (edist_ne_top v (it.toFun v))
  exact ⟨x, hr⟩

/-- Proof that the ConvIter.toFun has a fixpoint at the `x` from `Ax = b` -/
theorem solution_is_fixpt (it : ConvIter ι 𝕜) (x : ι → 𝕜) (heq: it.A *ᵥ x = it.b):
    Function.IsFixedPt it.toFun x := by
  haveI : Invertible it.M := it.inv
  rw [it.eq, add_mulVec] at heq
  apply eq_sub_of_add_eq at heq
  apply congr_arg (it.M⁻¹ *ᵥ ·) at heq
  rw [mulVec_mulVec, inv_mul_of_invertible, one_mulVec, mulVec_sub, mulVec_mulVec] at heq
  unfold Function.IsFixedPt
  rw [sub_eq_add_neg, ←neg_mulVec] at heq
  simp only [ConvIter.toFun, neg_mul]
  rw [add_comm, ←heq]

theorem iter_tendsto_solution (it : ConvIter ι 𝕜) (v x : ι → 𝕜) (h: it.A *ᵥ x = it.b):
    Filter.Tendsto (fun n ↦ it.toFun^[n] v) Filter.atTop (nhds x) := by
  let ⟨x', hic⟩ := iter_conv it v
  have : Filter.Tendsto (fun (_:Nat) => x) Filter.atTop (nhds x) := tendsto_const_nhds
  have hfe: (fun n => it.toFun^[n] x) = (fun n => x) := by
    funext n
    exact Function.iterate_fixed (solution_is_fixpt it x h) n
  rw [←hfe] at this
  have hf : ContractingWith ‖(-it.M⁻¹ * it.N).toLin'.toContinuousLinearMap‖₊ it.toFun :=
    iter_contracting it
  rw [ContractingWith.fixedPoint_unique hf (solution_is_fixpt it x h)]

  exact ContractingWith.tendsto_iterate_fixedPoint hf v
