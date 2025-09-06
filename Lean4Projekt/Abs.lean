import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic

variable {𝕜 ι: Type* }

instance [LE 𝕜] : LE (Matrix ι ι 𝕜) where
  le := fun A B => ∀ i j, A i j ≤ B i j

instance [LE 𝕜] [LT 𝕜] : LT (Matrix ι ι 𝕜) where
  lt := fun A B => A ≤ B ∧ ¬B ≤ A

theorem le_def [LE 𝕜] {A B : Matrix ι ι 𝕜} :
    A ≤ B ↔ ∀ i j, A i j ≤ B i j :=
  Iff.rfl

theorem lt_def [LE 𝕜] [LT 𝕜] {A B : Matrix ι ι 𝕜} :
    A < B ↔ A ≤ B ∧ ¬B ≤ A :=
  Iff.rfl

instance [Nonempty ι] [Preorder 𝕜] : Preorder (Matrix ι ι 𝕜) where
  le_refl : ∀ A, A ≤ A := fun A => by
    simp [le_def]
  le_trans : ∀ A B C, A ≤ B → B ≤ C → A ≤ C := by
    simp [le_def]
    intro A B C hAB hBC i j
    exact le_trans (hAB i j) (hBC i j)
  lt_iff_le_not_le : ∀ A B, A < B ↔ A ≤ B ∧ ¬B ≤ A := by
    simp [le_def, lt_def]


instance elementwiesePartialOrder [PartialOrder 𝕜] : PartialOrder (Matrix ι ι 𝕜) where
  le_antisymm := by
    simp [le_def]
    intro A B hAB hBA
    funext i j
    exact (hAB i j).antisymm (hBA i j)
  le_refl := by
    simp [le_def]
  le_trans := by
    simp [le_def]
    intro A B C hAB hBC i j
    exact le_trans (hAB i j) (hBC i j)


instance elementwiseInf [SemilatticeInf 𝕜] : SemilatticeInf (Matrix ι ι 𝕜) where
  inf := fun A B => fun i j => A i j ⊓ B i j
  inf_le_left := by
    simp [le_def]
  inf_le_right := by
    simp [le_def]
  le_inf := by
    simp [le_def]
    intro A B C hAB hAC i j
    exact ⟨hAB i j, hAC i j⟩

instance elementwiseSup [SemilatticeSup 𝕜] : SemilatticeSup (Matrix ι ι 𝕜) where
  sup := fun A B => fun i j => A i j ⊔ B i j
  le_sup_left := by
    simp [le_def]
  le_sup_right := by
    simp [le_def]
  sup_le := by
    simp [le_def]
    intro A B C hAB hAC i j
    exact ⟨hAB i j, hAC i j⟩

instance elementwiseLattice [Lattice 𝕜] : Lattice (Matrix ι ι 𝕜) where

theorem abs_apply [Lattice 𝕜] [AddGroup 𝕜] (M : Matrix ι ι 𝕜) (i j : ι) : |M| i j = |M i j| := by
    rw [← Pi.abs_apply, ← Pi.abs_apply]
