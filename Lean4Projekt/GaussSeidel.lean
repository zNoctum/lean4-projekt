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

import Lean4Projekt.Basic

open Matrix

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Lattice 𝕜] [IsOrderedAddMonoid 𝕜]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable instance : NormedAddCommGroup (Matrix ι ι 𝕜) := Matrix.linftyOpNormedAddCommGroup
instance : NormedSpace 𝕜 (Matrix ι ι 𝕜) := Matrix.linftyOpNormedSpace

variable [LinearOrder ι] [DecidableLT ι] [LocallyFiniteOrderBot ι] [LocallyFiniteOrderTop ι] [NormedAlgebra ℝ 𝕜]

variable (M : Matrix ι ι 𝕜)

def p (i : ι) : ℝ :=
    (∑ j : Finset.Iio i, ‖(M i j)/(M i i)‖ * p j) + ∑ j ∈ { j > i | j ∈ Finset.univ }, ‖(M i j)/(M i i)‖
  termination_by (Finset.Iio i).card
  decreasing_by
    apply Finset.card_lt_card
    apply Finset.Iio_ssubset_Iio
    exact Finset.mem_Iio.mp j.prop


def matrix_abs := of (fun i j => |M i j|)
notation "|" e "|" => matrix_abs e

def rel_lt (v w : ι → 𝕜) := ∀ i, (v - w) i > 0
infixr:40 " ≻ " => rel_lt
noncomputable def sassenfeld_circ := |1 - (diagonal M.diag)⁻¹ * M|
postfix:max "°" => sassenfeld_circ

def is_preconditioner := ‖M°‖₊ < 1 ∧ ∀ i, M i i ≠ 0
def pos_vec := { z : ι → 𝕜 // ∀ i, z i > 0 }

def off := M - (diagonal M.diag)

lemma lemma2_4 (ε : ℝ) (h : ε > 0) : ∃ z, (‖M‖ + ε) • z ≻ M *ᵥ z := by
  sorry

lemma lemma2_3 {P : Matrix ι ι 𝕜}:
    is_preconditioner P ↔ ∃ z, ∀ i, (|diagonal P.diag| *ᵥ z - |P - (diagonal P.diag)| *ᵥ z) i > 0 := by
  sorry


noncomputable def sassenfeld_idx (P : Matrix ι ι 𝕜) := ‖((1 - P°)⁻¹ * |diagonal P.diag|⁻¹ * |M - P|) *ᵥ 1‖₊

variable (b : ι → 𝕜)

noncomputable def gauss_seidel
    (P : Matrix ι ι 𝕜)
    (hp : is_preconditioner P)
    (hlp : sassenfeld_idx M P < 1)
      : ConvIter ι 𝕜 := by
  haveI : Invertible P := by
    have : ∀ x, ‖x‖₊ = 1 → P *ᵥ x = 0 → Invertible P := by
      intro x he hz
      have : x - (1 - (diagonal P.diag)⁻¹ * P) *ᵥ x = 0 := by
        rw [sub_mulVec, ←mulVec_mulVec, hz]
        simp
      have : P° *ᵥ |x| - |x| ≥ 0 := by sorry
      have hpb : 0 ≤ P°.toLin' |x| - |x| := by simp [this]
      have : ∀ n, 0 ≤ P°.toLin'^[n] |x| - |x| := by
        intro n
        induction n with
        | zero => simp
        | succ n' ihn' =>
          sorry

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


      apply lt_of_le_of_lt this
      exact hlp
}
