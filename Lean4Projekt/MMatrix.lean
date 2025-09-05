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
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Invertible
import Mathlib.Analysis.CStarAlgebra.Matrix

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable instance : NormedAddCommGroup (Matrix ι ι ℝ) := Matrix.linftyOpNormedAddCommGroup
noncomputable instance : NormedSpace ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedSpace
noncomputable instance : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing

theorem matrix_is_unit_smul {M : Matrix ι ι ℝ} {r : ℝ} (h : r ≠ 0) : IsUnit M ↔ IsUnit (r • M) := by
  apply Iff.intro <;> intro hu
  · rw [smul_eq_diagonal_mul]
    refine IsUnit.mul ?_ hu
    rw [isUnit_iff_isUnit_det, det_diagonal, IsUnit.prod_univ_iff]
    intro _
    exact isUnit_iff_ne_zero.mpr h
  · refine exists_right_inverse_iff_isUnit.mp ?_
    use r • ↑hu.unit⁻¹
    simp [inv_smul_eq_iff₀]
    haveI : Invertible (r • M) := hu.invertible
    rw [← smul_mul, Matrix.mul_inv_of_invertible]

structure MMatrix {ι : Type*} (M : Matrix ι ι ℝ) [Fintype ι] [DecidableEq ι] where
  is_unit : IsUnit M
  nonpos_off_diag : ∀ i j, i ≠ j → M i j ≤ 0
  nonneg_inv : ∀ i j, 0 ≤ M⁻¹ i j

variable [Nonempty ι]

theorem mmatrix_def (M : Matrix ι ι ℝ) : MMatrix M ↔ ∃ r : ℝ, ‖r • 1 - M‖ < r ∧ ∀ i j, 0 ≤ (r • 1 - M) i j := by
  apply Iff.intro
  · intro ⟨hu, hnp, hnni⟩
    let r := (Finset.univ.image (fun i => |M i i|)).max' (Finset.image_nonempty.mpr (Finset.univ_nonempty))
    use r
    have Bpos (i j) : 0 ≤ (r • 1 - M) i j := by
      rw [sub_apply, smul_apply, smul_eq_mul, sub_nonneg]
      by_cases h' : i = j
      · rw [h', Matrix.one_apply_eq, mul_one]
        dsimp [r]
        refine le_trans (le_abs_self (M j j)) ?_
        apply Finset.le_max' _ |M j j|
        simp
      · rw [Matrix.one_apply_ne h', mul_zero]
        exact hnp i j h'
    refine ⟨?_, Bpos⟩
    -- this is not really needed right now so keep it `sorry`ed.
    sorry
  · intro ⟨r, hle, hpos⟩
    let B := r • 1 - M
    have heq : M = r • 1 - B := by simp [B]
    have rge0 : 0 < r := by
      refine lt_of_le_of_lt ?_ hle
      simp
    have rnz : r ≠ 0 := Ne.symm (ne_of_lt rge0)
    have Brspec : ‖r⁻¹ • B‖₊ < 1 := by
      simp only [smul_apply, nnnorm_smul, ← Finset.mul_sum]
      have :  0 < ‖r‖₊ := by
        simp [rnz]
      rw [← mul_lt_mul_left this]
      have : ‖r‖₊ ≠ 0 := by
        simp [rnz]
      simp only [nnnorm_inv, ← mul_assoc, mul_inv_cancel₀ this, one_mul,
        mul_one]
      apply lt_of_lt_of_eq hle
      simp [abs_eq_self.mpr (le_of_lt rge0)]
    have hu : IsUnit M := by
      rw [heq]
      apply (matrix_is_unit_smul (inv_ne_zero rnz)).mpr
      rw [smul_sub, inv_smul_smul₀ rnz]
      exact isUnit_one_sub_of_norm_lt_one Brspec
    refine ⟨hu, ?_, ?_⟩
    · intro i j h
      rw [heq, sub_apply, smul_apply]
      by_cases h' : i = j
      · contradiction
      · rw [Matrix.one_apply_ne h', smul_zero]
        simpa [B] using hpos i j
    · intro i j
      have : M = r • (1 - r⁻¹ • B) := by
        rw [smul_sub, ← smul_assoc, smul_eq_mul, mul_inv_cancel₀ rnz, one_smul]
        exact heq
      rw [this]
      haveI : Invertible r := by exact invertibleOfNonzero rnz
      rw [inv_smul (k := r) (h := by
        rw [← isUnit_iff_isUnit_det]
        rw [matrix_is_unit_smul rnz, smul_sub, smul_smul, mul_inv_cancel₀ rnz, one_smul]
        exact heq ▸ hu
      )]
      rw [smul_apply, smul_eq_mul, ← mul_le_mul_iff_of_pos_left rge0]
      simp only [mul_zero, invOf_eq_inv, ← mul_assoc, mul_inv_cancel_of_invertible, one_mul]
      rw [nonsing_inv_eq_ringInverse, ← geom_series_eq_inverse (r⁻¹ • B) Brspec]
      have (i j) (n) : 0 ≤ ((r⁻¹ • B)^n) i j := by
        revert i j
        induction n with
        | zero =>
          intro i j
          rw [pow_zero]
          rw [Matrix.one_apply]
          by_cases i = j <;> simp [*]
        | succ n' ihn' =>
          intro i j
          rw [npow_add, pow_one, mul_apply]
          apply Finset.sum_nonneg
          intro i' _
          refine mul_nonneg (ihn' i i') ?_
          rw [← smul_le_smul_iff_of_pos_left rge0, smul_zero, smul_apply, ← smul_assoc]
          rw [smul_eq_mul r, mul_inv_cancel₀ rnz, one_smul]
          exact hpos i' j

      have smbl := HasSummableGeomSeries.summable_geometric_of_norm_lt_one (r⁻¹ • B) Brspec

      rw [tsum_apply smbl, tsum_apply (by
        revert i
        rw [← Pi.summable]
        exact smbl
      )]
      apply tsum_nonneg (this i j)
