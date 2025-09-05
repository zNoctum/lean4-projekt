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

import Lean4Projekt.Basic
import Lean4Projekt.MMatrix

open Matrix

-- Here we can't use a generic `𝕜` because we need the ability to multiply a value from the
-- field with a norm from another i.e. `∀ r s : 𝕜, r * ‖s‖` which is only given if `𝕜 = ℝ`
--variable {ℝ : Type*} [NontriviallyNormedField ℝ] [CompleteSpace ℝ] [LinearOrder ℝ] [IsOrderedAddMonoid ℝ] [ClosedIciTopology ℝ] [IsStrictOrderedRing ℝ] [NormedAlgebra ℝ ℝ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable instance : NormedAddCommGroup (Matrix ι ι ℝ) := Matrix.linftyOpNormedAddCommGroup
noncomputable instance : NormedSpace ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedSpace

variable (M : Matrix ι ι ℝ)

-- Elementwise absolute of a Matrix
def matrix_abs := of (fun i j => |M i j|)
notation "|" e "|" => matrix_abs e

noncomputable def circ := |1 - (diagonal M.diag)⁻¹ * M|
postfix:max "°" => circ

def IsPreconditioner := ‖M°‖₊ < 1

def off := M - (diagonal M.diag)

-- Proof that vector multiplication of matrices with only nonnegative entries is Monotone
theorem matrix_abs_mulVec_monotone : Monotone |M|.mulVec := by
  intro v w hle
  rw [Pi.le_def, mulVec_eq_sum, mulVec_eq_sum]
  simp
  intro i
  refine Finset.sum_le_sum ?_
  intro j _
  by_cases h : |M| i j = 0
  · simp [h]
  · refine mul_le_mul_of_nonneg_right (hle j) ?_
    exact abs_nonneg (M i j)

-- Proof that the monotonicity of `|M|` holds true even for repeated applications
theorem mon_iterate (n : ℕ) (v w : ι → ℝ) (h : v ≤ w) : |M|.mulVec^[n] v ≤ |M|.mulVec^[n] w := by
  induction n with
  | zero => simp [*]
  | succ n ihn =>
    rw [add_comm, Function.iterate_add_apply, Function.iterate_add_apply]
    rw [Function.iterate_one]
    rw [Pi.le_def]
    apply matrix_abs_mulVec_monotone
    assumption

theorem le_of_matrix_abs (v : ι → ℝ) : |M *ᵥ v| ≤ |M| *ᵥ |v| := by
  rw [Pi.le_def]
  intro i
  simp [mulVec_eq_sum]
  apply le_trans (show |∑ j, v j * M i j| ≤ ∑ j, |v j * M i j| by apply Finset.abs_sum_le_sum_abs (fun j => v j * M i j))
  refine Finset.sum_le_sum ?_
  intro j _
  dsimp [matrix_abs]
  rw [abs_mul (v j) (M i j)]

theorem nnnorm_le_nnnorm_of_abs_le_abs (v w : ι → ℝ) (h : |v| ≤ |w|) : ‖v‖₊ ≤ ‖w‖₊ := by
  rw [Pi.nnnorm_def, Pi.nnnorm_def]
  refine Finset.sup_mono_fun ?_
  intro i _
  exact h i

theorem nnnorm_le_nnnorm_of_abs_le (v w : ι → ℝ) (h : |v| ≤ w) : ‖v‖₊ ≤ ‖w‖₊ := by
  apply nnnorm_le_nnnorm_of_abs_le_abs
  intro i
  repeat rw [Pi.abs_apply]
  by_cases hw : w i < 0
  · specialize h i
    rw [Pi.abs_apply] at h
    apply le_trans (abs_nonneg (v i)) at h
    let contra := ne_of_lt <| lt_of_lt_of_le hw h
    contradiction
  · rw [abs_eq_self.mpr (le_of_not_lt hw)]
    exact h i

  -- Proof that all sassenfeld preconditioners are units. (Lemma 2.5 in the Paper)
theorem preconditioner_isUnit (P : Matrix ι ι ℝ) (h : IsPreconditioner P) : IsUnit P := by
  -- Convert Invertible P into Funtion.injective P.vecMul so we can show if P isn't Invertible
  -- there must be a vector x ≠ 0 with P *ᵥ x = 0
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

  -- This follows from `|A *ᵥ x| ≤ |A| *ᵥ |x|` and the definition of `P°`
  have bound (n) : |x| ≤ P°.mulVec^[n] |x| := by
    induction n with
    | zero => simp
    | succ n ihn =>
      simp at ihn ⊢
      apply le_trans ihn
      apply mon_iterate
      calc
        |x| = |x| := by rfl
        _ = |(1 - (diagonal P.diag)⁻¹ * P) *ᵥ x| := by simp [sub_mulVec, ←mulVec_mulVec, hPxz]
        _ ≤ P° *ᵥ |x| := by apply le_of_matrix_abs

  -- From `bound` we can now deduce that for `n → infinity` `P°^n |x| → 0`
  have lim (i): Filter.Tendsto (fun n => P°.toLin'^[n] |x| i) Filter.atTop (nhds 0) := by
    -- Proof that `P°` is a contraction this follows from the definition of a preconditioner
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
      exact ⟨h, this⟩
    apply tendsto_pi_nhds.mp
    -- Use the fact that `0` is a fix point for all linear functions
    -- and that there is only one Fixpoint because P° is a contraction
    let ⟨fix, _, hfix, _⟩ := ContractingWith.exists_fixedPoint con |x| (edist_ne_top |x| (P°.toLin' |x|))
    have : Filter.Tendsto (fun (n:Nat) => 0) Filter.atTop (nhds 0) := tendsto_const_nhds
    rw [← Pi.zero_def]
    rw [ContractingWith.fixedPoint_unique con (show Function.IsFixedPt P°.toLin' 0 by simp [Function.IsFixedPt])]
    exact ContractingWith.tendsto_iterate_fixedPoint con |x|

  -- Now because of the convergence we can infer that x must be zero which contradicts our assumption
  -- and thus our proof by contradiction is successful.
  have : |x| ≤ 0 := by
    intro i
    apply ge_of_tendsto' (lim i)
    intro n
    exact Pi.le_def.mp (bound n) i
  have : x = 0 := by
    funext i
    rw [Pi.zero_apply]
    specialize this i
    rw [Pi.zero_apply, Pi.abs_apply, abs_le'] at this
    apply eq_of_le_of_le
    · exact this.left
    · rw [← neg_zero, neg_le]
      exact this.right
  contradiction

theorem abs_diag : |diagonal M.diag| = diagonal |M|.diag := by
  funext i j
  simp [matrix_abs, diagonal]
  by_cases h : i = j <;> simp [*]

theorem abs_mul_diagonal (d : ι → ℝ) : diagonal |d| * |M| = |diagonal d * M| := by
  funext i j
  simp [matrix_abs, mul_diagonal]
  rw [abs_mul]

theorem abs_mul_diagonal' (P : Matrix ι ι ℝ) : diagonal |P|.diag * |M| = |diagonal P.diag * M| := by
  funext i j
  simp [matrix_abs, mul_diagonal]
  rw [abs_mul]

theorem preconditioner_diag_ne_zero (P : Matrix ι ι ℝ) (hp : IsPreconditioner P) (i : ι) : P i i ≠ 0 := by
  -- Proof by contradiction thus assuming `∃ i, P i i = 0`
  by_contra! h
  dsimp only [IsPreconditioner, circ] at hp
  rw [linfty_opNNNorm_def] at hp
  have : ∑ j, ‖|1 - (diagonal P.diag)⁻¹ * P| i j‖₊ < 1 := by
    apply lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ i))
    exact hp
  have h' : Ring.inverse P.diag i = Ring.inverse (P.diag i) := by
    by_cases hu : IsUnit P.diag
    · simp [Ring.inverse_of_isUnit hu]
    · simp [Ring.inverse_non_unit P.diag hu, h]
  -- Use the fact that `diagonal P.diag i = 0`
  -- this implies `P° i i = 1` which further implies `1 ≤ ‖P°‖₊` which is a contradiction to `hp`
  simp only [matrix_abs, inv_diagonal, sub_apply, diagonal_mul, of_apply, Real.nnnorm_abs] at this
  rw [h', diag_apply, h, Ring.inverse_zero] at this
  simp [one_apply, nnnorm_one, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at this

theorem abs_sub_comm' (N : Matrix ι ι ℝ) : |N - M| = |M - N| := by
  simp [matrix_abs]
  funext i j
  apply abs_sub_comm

theorem circ_alt_def {P : Matrix ι ι ℝ} (hp : IsPreconditioner P) : P° = diagonal |P.diag⁻¹| * |off P| := by
  dsimp only [circ]
  have : |off P| = |diagonal P.diag - P| := by
    simp [off, matrix_abs]
    funext i j
    rw [abs_sub_comm]
  rw [this, abs_mul_diagonal, mul_sub]
  simp
  have hPnz (i) : P i i ≠ 0 := preconditioner_diag_ne_zero P hp i
  have hu : IsUnit P.diag := by
    refine isUnit_diagonal.mp ?_
    rw [isUnit_iff_isUnit_det, det_diagonal]
    rw [@IsUnit.prod_univ_iff]
    intro i
    apply IsUnit.mk0
    rw [P.diag_apply]
    exact hPnz i
  have : (diagonal fun i ↦ (P i i)⁻¹ * P i i) = 1 := by
    funext i j
    simp [diagonal_apply]
    by_cases h : i = j <;> simp [*]
    simp [one_apply, h, inv_mul_cancel₀ (hPnz j)]
  simp [this, inv_diagonal, Ring.inverse_of_isUnit hu]

theorem mul_diagonl_inv_le (d v w : ι → ℝ) (hpos : ∀ i, 0 < d i) (h : diagonal d *ᵥ v ≤ w) : v ≤ (diagonal d)⁻¹ *ᵥ w := by
  intro i
  specialize h i
  have : IsUnit d := by
    refine isUnit_diagonal.mp ?_
    rw [isUnit_iff_isUnit_det, det_diagonal]
    rw [@IsUnit.prod_univ_iff]
    intro i
    apply IsUnit.mk0
    exact (ne_of_lt (hpos i)).symm

  rw [inv_diagonal, Ring.inverse_of_isUnit this]
  rw [mulVec_diagonal] at *
  simp only [Units.val_inv_eq_inv_val, IsUnit.unit_spec, ge_iff_le]
  rw [← mul_le_mul_iff_of_pos_left (hpos i), Pi.inv_apply, mul_inv_cancel_left₀ (ne_of_lt (hpos i)).symm]
  assumption

theorem one_sub_circ_is_mmatrix {P : Matrix ι ι ℝ} (hp : IsPreconditioner P) : MMatrix (1 - P°) := by
  rw [mmatrix_def (1 - P°)]
  use 1
  refine ⟨(by simpa using hp), ?_⟩
  intro i j
  simp only [one_smul, sub_apply, sub_sub_cancel]
  rw [circ, matrix_abs, of_apply]
  exact abs_nonneg ((1 - (diagonal P.diag)⁻¹ * P) i j)

theorem matrix_abs_eq_self {P : Matrix ι ι ℝ} (h : ∀ i j, 0 ≤ P i j) : |P| = P := by
  funext i j
  rw [matrix_abs, of_apply, abs_eq_self]
  exact h i j

theorem skk (a b c: ℝ) (h : |c| ≤ a):
    |b| ≤ a + |b + c| := by
  by_cases hb : 0 ≤ b <;>
  by_cases hc : 0 ≤ c
  any_goals apply le_of_not_le at hb
  any_goals apply le_of_not_le at hc
  any_goals rw [abs_eq_self.mpr hc] at h
  any_goals rw [abs_eq_neg_self.mpr hc] at h

  · rw [(abs_add_eq_add_abs_iff b c).mpr (Or.inl ⟨hb, hc⟩)]
    rw [abs_eq_self.mpr hb, abs_eq_self.mpr hc]
    linarith
  · obtain bc | bc := le_total (b + c) 0
    · rw [abs_eq_neg_self.mpr bc, abs_eq_self.mpr hb]
      rw [le_add_neg_iff_add_le]
      linarith
    · rw [abs_eq_self.mpr bc, abs_eq_self.mpr hb]
      linarith
  · obtain bc | bc := le_total (b + c) 0
    · rw [abs_eq_neg_self.mpr bc, abs_eq_neg_self.mpr hb]
      rw [le_add_neg_iff_add_le]
      simpa
    · rw [abs_eq_self.mpr bc, abs_eq_neg_self.mpr hb]
      linarith
  · rw [(abs_add_eq_add_abs_iff _ _).mpr (Or.inr ⟨hb, hc⟩)]
    rw [abs_eq_neg_self.mpr hb, abs_eq_neg_self.mpr hc]
    linarith

noncomputable def sassenfeld_idx (P : Matrix ι ι ℝ) := ‖((1 - P°)⁻¹ * |diagonal P.diag|⁻¹ * |M - P|) *ᵥ 1‖₊

variable (b : ι → ℝ)

noncomputable def gauss_seidel
    (P : Matrix ι ι ℝ)
    (hp : IsPreconditioner P)
    (hlp : sassenfeld_idx M P < 1)
      : ConvIter ι ℝ := by
  haveI : Invertible P := IsUnit.invertible (preconditioner_isUnit P hp)
  exact {
    A := M
    M := P
    b := b
    inv := inferInstance
    spec := by
      rw [← linfty_opNNNorm_toMatrix, LinearMap.coe_toContinuousLinearMap, LinearMap.toMatrix'_toLin']
      rw [Matrix.mul_sub]
      rw [neg_mul, neg_mul, inv_mul_of_invertible, sub_neg_eq_add, neg_add_eq_sub]

      -- use the fact that `sassenfeld_idx M P < 1` so we only need to prove `‖1 - P⁻¹ * M‖₊ ≤ sassenfeld_idx M P`
      -- and the apply the definition to the operator norm so that our goal becomes:
      -- `∀ y, ‖y‖₊ = 1 → ‖(1 - P⁻¹ * M) *ᵥ y‖₊ < 1`
      refine lt_of_le_of_lt ?_ hlp
      rw [linfty_opNNNorm_eq_opNNNorm]
      apply ContinuousLinearMap.opNNNorm_le_of_unit_nnnorm
      intro y hny
      simp only [ContinuousLinearMap.coe_mk', mulVecLin_apply, ge_iff_le]

      let R := P - M
      let x := (P⁻¹ * R) *ᵥ y
      have hx : (1 - P⁻¹ * M) *ᵥ y = x := by
        simp [x, R, mul_sub]

      apply nnnorm_le_nnnorm_of_abs_le
      rw [hx]

      have hxry : (diagonal P.diag) *ᵥ x + (off P) *ᵥ x = R *ᵥ y := by
        simp [R, x]
        rw [mul_sub, inv_mul_of_invertible]
        rw [← mulVec_mulVec, ← mulVec_mulVec, ← add_mulVec]
        simp only [off, add_sub_cancel, mulVec_mulVec, mul_sub, mul_one,
          mul_inv_cancel_left_of_invertible, x, R]

      haveI : Invertible (diagonal P.diag) := by
        -- A diagonal matrix is invertible if its determinant is
        apply invertibleOfIsUnitDet
        rw [det_diagonal]
        -- which in turn is a unit if all entries are nonzero
        apply isUnit_iff_ne_zero.mpr
        rw [Finset.prod_ne_zero_iff]
        -- which is already proven as `preconditioner_diag_ne_zero`
        intro i _
        exact preconditioner_diag_ne_zero P hp i

      have hylt1 : |R| *ᵥ |y| ≤ |R| *ᵥ 1 := by
        -- use the fact that the entrywise abs of a matrix is monotone so we only have to prove:
        -- `⊢ ∀i, |y| i ≤ 1`
        apply matrix_abs_mulVec_monotone
        intro i
        have : |y| i ≤ ‖y‖ := by
          rw [Pi.norm_def]
          refine le_trans ?_ (Finset.le_sup (Finset.mem_univ i) (f := (‖y ·‖₊)))
          simp
        apply le_of_eq at hny
        rw [← coe_nnnorm y] at this
        exact le_trans this hny

      have : (|diagonal P.diag| * (1 - P°)) *ᵥ |x| ≤ |R| *ᵥ |y| := by
        simp [mul_sub, circ_alt_def hp]
        have : (diagonal fun i => |P|.diag i * |P.diag⁻¹| i) = 1 := by
          funext i j
          by_cases he : i = j
          · simp [diagonal_apply_eq, he]
            rw [abs_inv, matrix_abs, of_apply]
            simp only [one_apply, he, ↓reduceIte, x, R]
            haveI : Invertible |P j j| := by
              refine invertibleOfNonzero ?_
              apply abs_by_cases (· ≠ 0)
              <;> simp [preconditioner_diag_ne_zero P hp j, *]
            rw [mul_inv_cancel_of_invertible]
          · simp [diagonal_apply_ne, he]
        rw [abs_diag, ← mul_assoc, diagonal_mul_diagonal, this]
        simp []

        refine le_trans ?_ (le_of_matrix_abs R y)
        rw [← hxry]
        apply (add_le_add_iff_left (|off P| *ᵥ |x|)).mp
        rw [← add_mulVec]
        rw [Pi.le_def]
        intro i
        simp
        have (i) : (diagonal |P|.diag *ᵥ |x|) i = |(diagonal P.diag *ᵥ x) i| := by
          simp [mulVec_diagonal, matrix_abs, abs_mul]
        rw [this]

        apply skk

        revert i
        rw [← Pi.le_def, ← Pi.abs_def]
        exact le_of_matrix_abs (off P) x

      have : (|diagonal P.diag| * (1 - P°)) *ᵥ |x| ≤ |R| *ᵥ 1 := le_trans this hylt1

      rw [← mulVec_mulVec] at this
      have : (1 - P°) *ᵥ |x| ≤ |diagonal P.diag|⁻¹ *ᵥ |R| *ᵥ 1 := by
        rw [abs_diag] at this ⊢
        apply mul_diagonl_inv_le
        · intro i
          simp only [matrix_abs, diag_apply, of_apply, abs_pos, x, R]
          exact preconditioner_diag_ne_zero P hp i
        · assumption

      have : |x| ≤ (1 - P°)⁻¹ *ᵥ |diagonal P.diag|⁻¹ *ᵥ |R| *ᵥ 1 := by
        apply matrix_abs_mulVec_monotone (1 - P°)⁻¹ at this
        rw [matrix_abs_eq_self ((one_sub_circ_is_mmatrix hp).nonneg_inv)] at this
        simp at this
        haveI I : Invertible (1 - P°) := (one_sub_circ_is_mmatrix hp).is_unit |> IsUnit.invertible
        rw [Matrix.inv_mul_of_invertible (1 - P°), one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec] at this
        exact this
      simp [R, ← mul_assoc] at this
      rw [abs_sub_comm' M P] at this
      exact this
}
