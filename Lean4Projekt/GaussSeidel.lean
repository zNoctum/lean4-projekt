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
import Mathlib.Topology.Constructions
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Group.Invertible.Basic

import Lean4Projekt.Basic

open Matrix

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [DistribLattice 𝕜] [IsOrderedAddMonoid 𝕜] [ClosedIciTopology 𝕜]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable instance : NormedAddCommGroup (Matrix ι ι 𝕜) := Matrix.linftyOpNormedAddCommGroup
instance : NormedSpace 𝕜 (Matrix ι ι 𝕜) := Matrix.linftyOpNormedSpace

variable [LinearOrder ι] [DecidableLT ι] [LocallyFiniteOrderBot ι] [LocallyFiniteOrderTop ι] [NormedAlgebra ℝ 𝕜] [LinearOrder 𝕜]

variable (M : Matrix ι ι 𝕜)

def p (i : ι) : ℝ :=
    (∑ j : Finset.Iio i, ‖(M i j)/(M i i)‖ * p j) + ∑ j ∈ { j > i | j ∈ Finset.univ }, ‖(M i j)/(M i i)‖
  termination_by (Finset.Iio i).card
  decreasing_by
    apply Finset.card_lt_card
    apply Finset.Iio_ssubset_Iio
    exact Finset.mem_Iio.mp j.prop


def matrix_abs := of (fun i j => |M i j|)
def vabs (v : ι → 𝕜) := (fun i => |v i|)
notation "|" e "|" => matrix_abs e

noncomputable def sassenfeld_circ := |1 - (diagonal M.diag)⁻¹ * M|
postfix:max "°" => sassenfeld_circ

def is_preconditioner := ‖M°‖₊ < 1 ∧ ∀ i, M i i ≠ 0
def pos_vec := { z : ι → 𝕜 // ∀ i, z i > 0 }

def off := M - (diagonal M.diag)

lemma lemma2_3 {P : Matrix ι ι 𝕜}:
    is_preconditioner P ↔ ∃ z, ∀ i, (|P - (diagonal P.diag)| *ᵥ z) i < (|diagonal P.diag| *ᵥ z) i := by
  sorry


noncomputable def sassenfeld_idx (P : Matrix ι ι 𝕜) := ‖((1 - P°)⁻¹ * |diagonal P.diag|⁻¹ * |M - P|) *ᵥ 1‖₊

variable (b : ι → 𝕜)

noncomputable def gauss_seidel
    (P : Matrix ι ι 𝕜)
    (hp : is_preconditioner P)
    (hlp : sassenfeld_idx M P < 1)
      : ConvIter ι 𝕜 := by
  -- Prove invertability of all sassenfeld preconditioners. (Lemma 2.5 in the Paper)
  haveI : Invertible P := by
    -- Convert Invertible P into Funtion.injective P.vecMul so we can show if P isn't Invertible
    -- there must be a vector x ≠ 0 with P *ᵥ x = 0
    refine IsUnit.invertible ?_
    rw [← mulVec_injective_iff_isUnit]
    by_contra!
    simp [Function.Injective] at this
    let ⟨v,w,he,hne⟩ := this
    let x := v - w
    have hPxz : P *ᵥ x = 0 := by
      simp [x, mulVec_sub, he]
    have hxnz : x ≠ 0 := by
      dsimp only [x]
      by_contra!
      rw [sub_eq_zero] at this

      contradiction

    have : x - (1 - (diagonal P.diag)⁻¹ * P) *ᵥ x = 0 := by
      simp [sub_mulVec, ←mulVec_mulVec, hPxz]

    have : ∀ i n,  (|x ·|) i ≤ (P°.toLin'^[n] (|x ·|)) i := by
      intro i n
      induction n with
      | zero => simp
      | succ n ihn =>
        simp at ihn ⊢
        apply le_trans ihn
        sorry
    have lim : ∀ i, Filter.Tendsto (fun n => (P°.toLin'^[n] (|x ·|)) i) Filter.atTop (nhds 0) := by
      have con : ContractingWith ‖P°‖₊ P°.toLin' := by
        let hl := ContinuousLinearMap.lipschitz P°.toLin'.toContinuousLinearMap
        have : ‖P°‖₊ = ‖P°.toLin'.toContinuousLinearMap‖₊ := by
          rw [linfty_opNNNorm_eq_opNNNorm, ContinuousLinearMap.nnnorm_def, ContinuousLinearMap.nnnorm_def]
          rfl
        have : LipschitzWith ‖P°‖₊ P°.toLin' := by
          intro v w
          specialize hl v w
          simp at hl ⊢
          rw [this]
          assumption
        exact ⟨hp.left, this⟩

      apply tendsto_pi_nhds.mp
      let ⟨fix, _, hfix, _⟩ := ContractingWith.exists_fixedPoint con (|x ·|) (edist_ne_top (|x ·|) (P°.toLin' (|x ·|)))
      have : Filter.Tendsto (fun (n:Nat) => 0) Filter.atTop (nhds 0) := tendsto_const_nhds
      rw [← Pi.zero_def]
      rw [ContractingWith.fixedPoint_unique con (show Function.IsFixedPt P°.toLin' 0 by simp [Function.IsFixedPt])]
      exact ContractingWith.tendsto_iterate_fixedPoint con (|x ·|)

    have : ∀ i, |x i| ≤ 0 := by
      intro i
      specialize this i
      apply ge_of_tendsto' (lim i)
      exact this
    have : x = 0 := by
      funext i
      rw [Pi.zero_apply]
      specialize this i
      rw [abs_le'] at this
      apply eq_of_le_of_le
      · exact this.left
      · rw [← neg_zero, neg_le]
        exact this.right
    contradiction
  exact {
    A := M
    M := P
    b := b
    inv := by infer_instance
    spec := by
      rw [← linfty_opNNNorm_toMatrix, LinearMap.coe_toContinuousLinearMap, LinearMap.toMatrix'_toLin']
      rw [Matrix.mul_sub]
      rw [neg_mul, neg_mul, inv_mul_of_invertible, sub_neg_eq_add, neg_add_eq_sub]
      have : ‖1 - P⁻¹ * M‖₊ ≤ sassenfeld_idx M P := by
        let R := P - M
        have : ∀ y : ι → 𝕜, ‖y‖₊ = 1 → ‖1 - P⁻¹ * M‖₊ ≤ sassenfeld_idx M P := by
          intro y he
          let x := (P⁻¹ * R) *ᵥ y
          have : (diagonal P.diag) *ᵥ x + (off P) *ᵥ x = R *ᵥy := by
            simp [R, x]
            rw [mul_sub, inv_mul_of_invertible]
            sorry
          sorry
        sorry
      apply lt_of_le_of_lt this
      exact hlp
}
