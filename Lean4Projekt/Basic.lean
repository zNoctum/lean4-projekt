import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Order.Field.Basic

section
variable {K : Type*} [LinearOrderedField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (β : LinearMap.BilinForm K V)



theorem generic_diag (hadd : (1:K) + (1:K) ≠ (0:K)) (hsymm : β.IsSymm):
    ∃B : Basis (Fin (Module.finrank K V)) K V, Matrix.IsDiag (BilinForm.toMatrix B β)
  := by
  sorry

theorem nullraum (B : Basis (Fin (Module.finrank K V)) K V) (hdiag : Matrix.IsDiag (BilinForm.toMatrix B β)) (v : V):
    forall w : V, β v w = 0 <-> ↑(B.repr v).support ⊆ {i | β (B i) (B i) = 0}
     := by sorry

end

section

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable (r_pos r_neg r_zero : Nat)
def d (i : Fin (Module.finrank ℝ V)): ℝ := if i.toNat < r_pos then 1 else if i.toNat < r_pos + r_neg then -1 else 0

variable (β : LinearMap.BilinForm ℝ V)

def MaxDim (n : Nat) (c : Submodule ℝ V → Prop) := (∀ W : Submodule ℝ V, c W → Module.finrank ℝ W ≤ n) ∧ (∃ W : Submodule ℝ V, (c W ∧ Module.finrank ℝ W = n))

theorem sylvester (hpos  : MaxDim r_pos  (∀ w ∈ ·, w ≠ 0 → (β w w > 0)))
                  (hneg  : MaxDim r_neg  (∀ w ∈ ·, w ≠ 0 → (β w w < 0)))
                  (hzero : MaxDim r_zero (∀ w ∈ ·, ∀ v : V, β w v = 0)):
    ∃B : Basis (Fin (Module.finrank ℝ V)) ℝ V, Matrix.diagonal (d r_pos r_neg) = BilinForm.toMatrix B β := by
  sorry


end

-- variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

--variable (β : LinearMap.BilinForm ℝ V)
--variable (B : Basis (Fin (Module.finrank ℝ V)) ℝ V)

-- theorem bilin_diag (h : β.IsSymm):
--    ∃B : Basis (Fin (Module.finrank ℝ V)) ℝ V, Matrix.IsDiag (BilinForm.toMatrix B β)
--  := by
--    sorry

--theorem vvv (h : β.IsSymm) (h₁ : Matrix.IsDiag (BilinForm.toMatrix B β)):


--theorem sylvester (h : β.IsSymm):
--    ∃d : Fin (Module.finrank ℝ V) → ℝ,
--    ∀x : Fin (Module.finrank ℝ V), d x = 1 ∨ d x = -1 ∨ d x = 0 →
--      ∃B : Basis (Fin (Module.finrank ℝ V)) ℝ V,
--        BilinForm.toMatrix B β = Matrix.diagonal d
--  := by
--  sorry
