
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.LinearMap
import Playground.TensorBundle

namespace Playground
noncomputable section

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I ω M]
variable {x' : M}

abbrev TrivialBundle : M → Type _ := fun _ ↦  𝕜

@[reducible]
def CotangentSpace (I : ModelWithCorners 𝕜 E H) (x : M) :=
  TangentSpace I x →L[𝕜] 𝕜

noncomputable instance : ContMDiffVectorBundle
   n (E →L[𝕜] 𝕜) (fun x : M => CotangentSpace I x) I := by
  infer_instance

/-- The index set for the coordinate frame; uses the basis of the model space E -/
abbrev CoordinateFrameIndex (𝕜 : Type*) [DivisionRing 𝕜]
    (E : Type*) [AddCommGroup E] [Module 𝕜 E] : Set E :=
  Module.Basis.ofVectorSpaceIndex 𝕜 E


/--
The coordinate representation of a vector field with respect to the extended chart at `x₀`.

Given a vector field `V` and a point `x` in the manifold, this function computes the coordinates
of the tangent vector `V x` by applying the manifold derivative of the extended chart.
The result is an element of `E`, representing the vector in the standard basis of the model space.

This is only defined for points `x` in the source of the extended chart.
-/
noncomputable def vectorFieldCoordinates
    (V : Π (x : M), TangentSpace I x)
    (x₀ : M)  -- center of the chart
    (x : M)   -- point where we evaluate the coordinates
    : E :=
  mfderiv I 𝓘(𝕜, E) (extChartAt I x₀) x (V x)


noncomputable def vectorFieldCoordinatesAt
    (V : Π (x : M), TangentSpace I x)
    (x₀ : M)  -- point determining the chart
    (x : M)   -- point where we evaluate
    : E :=
  vectorFieldCoordinates V x₀ x

#check vectorFieldCoordinates




variable (V : Π (x : M), TangentSpace I x) (x₀ x : M)

/-- Unfold the definition in terms of mfderiv -/
lemma def_eq :
    vectorFieldCoordinates V x₀ x = mfderiv I 𝓘(𝕜, E) (extChartAt I x₀) x (V x) :=
  rfl

#check @TangentBundle

noncomputable instance : ContMDiffVectorBundle
   n E (fun x : M => TangentSpace I x) I := by
  infer_instance


lemma smooth_of_smooth_vectorfield
    (hV : ContMDiff I I.tangent ω (fun y ↦ (V y : TangentBundle I M))) :
    ContMDiffOn I 𝓘(𝕜, E) ω
      (fun x ↦ vectorFieldCoordinates V x₀ x)
      (extChartAt I x₀).source := by
  intro x hx
  simp only [vectorFieldCoordinates]

  have hs_uniq : UniqueMDiffOn I (extChartAt I x₀).source :=
   (isOpen_extChartAt_source x₀).uniqueMDiffOn

  have h_tangent : ContMDiffOn I.tangent 𝓘(𝕜, E).tangent ω
      (tangentMapWithin I 𝓘(𝕜, E) (extChartAt I x₀) (extChartAt I x₀).source)
      (Bundle.TotalSpace.proj ⁻¹' (extChartAt I x₀).source) := by
    have step1 : ContMDiffOn I 𝓘(𝕜, E) ω (extChartAt I x₀) (chartAt H x₀).source :=
      contMDiffOn_extChartAt
    have step2 : UniqueMDiffOn I (chartAt H x₀).source :=
      (chartAt H x₀).open_source.uniqueMDiffOn
    have step3 := step1.contMDiffOn_tangentMapWithin (m := ω) le_top step2
    rw [extChartAt_source I x₀]
    exact step3

  have h_comp : ContMDiffOn I 𝓘(𝕜, E).tangent ω
      (fun y ↦ tangentMapWithin I 𝓘(𝕜, E) (extChartAt I x₀) (extChartAt I x₀).source ⟨y, V y⟩)
      (extChartAt I x₀).source := by
    apply ContMDiffOn.comp h_tangent hV.contMDiffOn
    intro y hy
    exact hy

  have h_snd: ContMDiff 𝓘(𝕜, E).tangent 𝓘(𝕜, E) ω
      (fun p : TangentBundle 𝓘(𝕜, E) E ↦ p.2) :=
    contMDiff_snd_tangentBundle_modelSpace (n := ω) E 𝓘(𝕜, E)

  -- Compose to get the second component
  have h_final : ContMDiffOn I 𝓘(𝕜, E) ω
      (fun y ↦ (tangentMapWithin I 𝓘(𝕜, E) (extChartAt I x₀) (extChartAt I x₀).source ⟨y, V y⟩).2)
      (extChartAt I x₀).source :=
    h_snd.comp_contMDiffOn h_comp

  -- tangentMapWithin.2 = mfderivWithin = mfderiv (by uniqueness)
  have h_eq : ∀ y ∈ (extChartAt I x₀).source,
      (tangentMapWithin I 𝓘(𝕜, E) (extChartAt I x₀) (extChartAt I x₀).source ⟨y, V y⟩).2 =
      mfderiv I 𝓘(𝕜, E) (extChartAt I x₀) y (V y) := by
    intro y hy
    simp only [tangentMapWithin]
    congr 1
    apply mfderivWithin_eq_mfderiv (hs_uniq y hy)
    have hy' : y ∈ (chartAt H x₀).source := by rwa [← extChartAt_source I x₀]
    have h_nhds : (chartAt H x₀).source ∈ 𝓝 y := (chartAt H x₀).open_source.mem_nhds hy'
    exact (contMDiffOn_extChartAt.mdifferentiableOn le_top y hy').mdifferentiableAt h_nhds

  exact (h_final x hx).congr (fun y hy => (h_eq y hy).symm) (h_eq x hx).symm


#check tangentMapWithin_eq_tangentMap
#check @tangentMapWithin_eq_tangentMap
#check contMDiff_snd_tangentBundle_modelSpace
