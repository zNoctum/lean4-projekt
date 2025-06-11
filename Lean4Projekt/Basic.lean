import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Matrix.Reflection

open Matrix
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Countable 𝕜]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [PartialOrder ι] [DecidableLT ι] [DecidableLE ι] [LocallyFiniteOrderTop ι] [LocallyFiniteOrderBot ι]

variable (v₀ : (ι → 𝕜))
variable (x : (ι → 𝕜))

noncomputable def ρ (φ : (ι → 𝕜) →ᵃ[𝕜] (ι → 𝕜)) := spectralRadius 𝕜 (φ.linear.toContinuousLinearMap)

variable (φ : (ι → 𝕜) →ᵃ[𝕜] (ι → 𝕜))

#check edist

theorem iter_conv (hspec: ‖φ.linear.toContinuousLinearMap‖₊ < 1):
    ∃ x : ι → 𝕜, Filter.Tendsto (fun n => φ.toFun^[n] v₀) Filter.atTop (nhds x) := by
  have hz : ∀ v : ι → 𝕜, v = v +ᵥ (λ _ => (0 : 𝕜)) := by
    intro v
    simp [Pi.zero_def]“
    let K := ContinuousLinearMap.lipschitz φ.linear.toContinuousLinearMap
    simp[LipschitzWith] at K
    specialize K v w
    rw [edist_nndist, nndist_edist] at K
    exact K
  have hf: ContractingWith ‖φ.linear.toContinuousLinearMap‖₊ φ.toFun := ⟨hspec, hl⟩
  let ⟨x, _, hr, _⟩ := ContractingWith.exists_fixedPoint hf v₀ (edist_ne_top v₀ (φ.toFun v₀))
  exact ⟨x, hr⟩


variable (M : Matrix ι ι 𝕜)
variable (b : ι → 𝕜)

noncomputable def to_affine : (ι → 𝕜) →ᵃ[𝕜] (ι → 𝕜) :=
  ⟨(λ v => M *ᵥ v + b), (Matrix.toLin' M), (λ p v => by simp; rw [←add_assoc, ←mulVec_add])⟩

noncomputable def jacobi : (ι → 𝕜) →ᵃ[𝕜] (ι → 𝕜) :=
  to_affine (λ i j => if i = j then 0 else -(M i i)⁻¹ * (M i j)) (λ i => (M i i)⁻¹ * (b i))

theorem iter_conv_jacobi (heq : M *ᵥ x = b) (hspec: ‖(jacobi M b).linear.toContinuousLinearMap‖₊ < 1):
    Filter.Tendsto (fun n => (jacobi M b).toFun^[n] v₀) Filter.atTop (nhds x) := by
  let ⟨x', hconv⟩ := iter_conv v₀ (jacobi M b) hspec
  have h : x' = x := by
    simp [jacobi] at hconv
    sorry
  rw [h] at hconv
  exact hconv

@[simp]
def diag_dominant :=
  ∀ i : ι, (∑ j ∈ Finset.univ.erase i, ‖M i j‖) < ‖M i i‖

theorem jacobi_conv_diag_dominant (h : diag_dominant (jacobi M b).linear.toMatrix'):
    ‖(jacobi M b).linear.toContinuousLinearMap‖₊ < 1 := by
  sorry

noncomputable def gauss_seidel : (ι → 𝕜) →ᵃ[𝕜] (ι → 𝕜) :=
  let B := Matrix.of (λ i j => if j ≤ i then M i j else 0)
  let A := Matrix.of (λ i j => if j ≤ i then 0 else M i j)
  to_affine (-B⁻¹ * A) (B⁻¹ *ᵥ b)

def BIio (i : ι) : { s : Finset ι // ∀ j ∈ s, j < i } := ⟨Finset.Iio i, (λ _ h => Finset.mem_Iio.mp h)⟩

def p (i : ι) : ℝ :=
    (∑ j : BIio i, ‖(M i j)/(M i i)‖ * p j) + ∑ j ∈ { j > i | j ∈ Finset.univ }, ‖(M i j)/(M i i)‖
  termination_by (Finset.Iio i).card
  decreasing_by
    apply Finset.card_lt_card
    let h := j.prop
    dsimp [BIio] at h
    apply Finset.Iio_ssubset_Iio
    exact Finset.mem_Iio.mp h

#check p M

theorem iter_conv_gauss_seidel (heq : M *ᵥ x = b) (hspec: ρ (gauss_seidel M b) < 1):
    Filter.Tendsto (fun n => (gauss_seidel M b).toFun^[n] v₀) Filter.atTop (nhds x) := by
  sorry

theorem sassenfeld_crit (h : ∀ i : ι, p M i < 1):
    ρ (gauss_seidel M b) < 1 := by
  sorry
