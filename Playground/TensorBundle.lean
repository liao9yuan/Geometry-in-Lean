/- This file defines tensor bundle on a smooth manifold by the follwoing

Let `M` be a manifold with model `I` on `(E, H),` whereas we assumed that `M` has finite dimension
The tangent space `TangentSpace I (x : M)` has already been defined as a type synonym for `E`,
and the tangent bundle `TangentBundle I M` as an abbrev of `Bundle.TotalSpace E (TangentSpace I : M → Type _)`.

The cotangent space `CotangentSpace I (x : M)` is the dual TangentSpace I x →L[𝕜] 𝕜 and `CotangentBundle`
is defined similarily to `TangentBundle` as to `TangentSpace I (x:M),` namely to be abbreviation
Bundle.TotalSpace (E →L[𝕜] 𝕜) (CotangentSpace I: M → Type _)

We then define `TensorR0Space (r : ℕ)` by r-mutlilinear map to `CotangentSpace,` which in finite dimension
isomorphic to the (r,0) tensors. Consideration for Banach manifold is left for a future project.
`TensorR0Bundle` is the abbrevation Bundle.TotalSpace (TensorRSModel 𝕜 E r s) (TensorRSSpace r s I : M → Type _)

After some clearance of inference problem, we inductively construct a structure `tensorBundleData (r: ℕ)`
which stores four instances `topology` `fiber` `vector` `smooth,` that the (r,0) tensor bundle is
a topological space, a fibre bundle, a vector bundle, and a smooth vector bundle respectively.

We finally define (r,s) tensor bundle as the hom bundle from (s,0) tensor bundle to (r,0) tensor bundle,
then show the instance `tensorRSBundle_smooth (r s : ℕ)`
  ContMDiffVectorBundle n
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => TensorR0Space s I x →L[𝕜] TensorR0Space r I x) I

To do:
verify actually (1,0) bundle is tangent bundle
Einstein convention/ Frame Bundle?
Lie Derivative
-/


import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.LinearMap

namespace TensorBundle
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


noncomputable instance (r : ℕ) :
    NormedAddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜) :=
  @ContinuousLinearMap.toNormedAddCommGroup 𝕜 𝕜
    (E →L[𝕜] 𝕜) (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id 𝕜)
    inferInstance

noncomputable def tensorR0_curry
    (r : ℕ) (x : M) :
  ContinuousMultilinearMap 𝕜 (fun _ : Fin (r+1) => CotangentSpace I x) 𝕜
    ≃L[𝕜]
  (CotangentSpace I x →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜) := by
  unfold CotangentSpace
  exact (continuousMultilinearCurryLeftEquiv 𝕜
    (fun _ : Fin (r+1) => E →L[𝕜] 𝕜) 𝕜).toContinuousLinearEquiv

-- Fiberwise instances for (r,0)-tensors
noncomputable instance tensorR0Space_normedAddCommGroup (r : ℕ) (x : M) :
    NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜) :=
  inferInstance

noncomputable instance tensorR0Space_normedSpace (r : ℕ) (x : M) :
    NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜) :=
  inferInstance

-- Fiberwise instances for (r,s)-tensors
noncomputable instance tensorRSSpace_normedAddCommGroup (r s : ℕ) (x : M) :
    NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => CotangentSpace I x) 𝕜 →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜) :=
  inferInstance

noncomputable instance tensorRSSpace_normedSpace (r s : ℕ) (x : M) :
    NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => CotangentSpace I x) 𝕜 →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜) :=
  inferInstance



noncomputable instance tensorRSSpace_continuousSMul (r s : ℕ) (x : M) :
    ContinuousSMul 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => CotangentSpace I x) 𝕜 →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜) :=
  inferInstance

noncomputable instance tensorRSModel_topology (r s : ℕ) :
    TopologicalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜) :=
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜) := inferInstance
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜) := inferInstance
  inferInstance

noncomputable instance tensorR0Model_normedAddCommGroup (r : ℕ) :
    NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜) :=
  inferInstance

noncomputable instance tensorR0Model_normedSpace (r : ℕ) :
    NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜) :=
  inferInstance

-- Model fiber instances for (r,s)-tensors
noncomputable instance tensorRSModel_normedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜) :=
  inferInstance

noncomputable instance tensorRSModel_normedSpace (r s : ℕ) :
    NormedSpace 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜) :=
  inferInstance



-- Topology instances for (0,0)-tensor bundle
noncomputable instance tensorR0_topologicalSpace_zero :
    TopologicalSpace (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => CotangentSpace I x) 𝕜)) := by
  have h : (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => CotangentSpace I x) 𝕜) =
           (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜) := by
    ext x
    unfold CotangentSpace
    rfl
  rw [h]
  infer_instance

noncomputable instance tensorR0_fiberBundle_zero :
    FiberBundle
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => CotangentSpace I x) 𝕜) :=
     inferInstanceAs <| FiberBundle
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)

noncomputable instance tensorR0_vectorBundle_zero :
    VectorBundle 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => CotangentSpace I x) 𝕜) :=
     inferInstanceAs <| VectorBundle 𝕜
       (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
        (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)

noncomputable instance tensorR0_contMDiffVectorBundle_zero :
    ContMDiffVectorBundle n
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => CotangentSpace I x) 𝕜) I :=
    inferInstanceAs <| ContMDiffVectorBundle n
       (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
       (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜) I

structure TensorBundleData (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (H : Type*) [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (n : WithTop ℕ∞) [IsManifold I n M]
    (r : ℕ) where
  topology : TopologicalSpace (TotalSpace
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
    (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜))
  fiber : FiberBundle
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
    (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜)
  vector : VectorBundle 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
    (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜)
  smooth : ContMDiffVectorBundle n
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
    (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜) I


noncomputable def tensorBundleData_zero :
    TensorBundleData (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) 0 := {
  topology := tensorR0_topologicalSpace_zero
  fiber := tensorR0_fiberBundle_zero
  vector := tensorR0_vectorBundle_zero
  smooth := inferInstanceAs <| ContMDiffVectorBundle n
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
    (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜) I
}

noncomputable instance tensorBundleData : (r : ℕ) →
    TensorBundleData (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
  | 0 => tensorBundleData_zero  (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n)
  | r + 1 => by
    let prev := tensorBundleData r
    refine {
      topology := ?_,
      fiber := ?_,
      vector := ?_,
      smooth := ?_
    }
    · have h : (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin (r+1) => CotangentSpace I x) 𝕜) =
              (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin (r+1) => E →L[𝕜] 𝕜) 𝕜) := by
        ext x
        unfold CotangentSpace
        rfl
      rw [h]
      infer_instance
    · exact inferInstanceAs <| FiberBundle
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (r+1) => E →L[𝕜] 𝕜) 𝕜)
        (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin (r+1) => E →L[𝕜] 𝕜) 𝕜)
    · exact inferInstanceAs <| VectorBundle 𝕜
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (r+1) => E →L[𝕜] 𝕜) 𝕜)
        (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin (r+1) => E →L[𝕜] 𝕜) 𝕜)
    · haveI : ContMDiffVectorBundle n (E →L[𝕜] 𝕜)
        (fun x : M => CotangentSpace I x) I := inferInstance
      exact inferInstanceAs <| ContMDiffVectorBundle n
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (r+1) => E →L[𝕜] 𝕜) 𝕜)
        (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin (r+1) => E →L[𝕜] 𝕜) 𝕜) I

instance tensorR0Bundle_topology (r : ℕ) :
    TopologicalSpace (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜)) :=
  (tensorBundleData n r).topology

@[simp]
noncomputable instance tensorR0Bundle_fiber (r : ℕ) :
    @FiberBundle
      M
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      _
      _
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜)
      (tensorR0Bundle_topology (n := n) r)
      _
      :=
  (@tensorBundleData 𝕜 _ E _ _ _ H _ I M _ _ n _ r).fiber

@[simp]
noncomputable instance tensorR0Bundle_vector (r : ℕ) :
    @VectorBundle
      𝕜
      M
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜)
      _
      _
      _
      _
      _
      _
      (tensorR0Bundle_topology (n := n) r)
      _
      (tensorBundleData n r).fiber
      :=
  (tensorBundleData (n := n) r).vector

@[simp]
noncomputable instance tensorR0Bundle_smooth (r : ℕ) :
    @ContMDiffVectorBundle
      n
      𝕜
      M
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜)
      _
      E
      _
      _
      H
      _
      I
      _
      _
      _
      _
      _
      _
      (tensorR0Bundle_topology (n := n) r)
      _
      (tensorBundleData n r).fiber
      (tensorBundleData n r).vector
      :=
  (tensorBundleData (n := n) r).smooth

#check tensorR0Bundle_smooth n 5

-- Topology for (r,s)-tensor bundles
noncomputable instance tensorRSBundle_topology (r s : ℕ) :
    TopologicalSpace (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => CotangentSpace I x) 𝕜 →L[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜)) := by
    letI := tensorR0Bundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensorR0Bundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensorR0Bundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    exact Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜)
      (fun (x : M) => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => CotangentSpace I x) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun (x : M) => ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜)

#check (tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) 5 6)

-- Fiber bundle instance for (r,s)-tensors
noncomputable instance tensorRSBundle_fiber (r s : ℕ) :
    @FiberBundle
      M
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      _
      (by infer_instance : TopologicalSpace _)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => CotangentSpace I x) 𝕜 →L[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜)
      (tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      _
      := by
    letI := tensorR0Bundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensorR0Bundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensorR0Bundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI : ∀ (x : M), IsTopologicalAddGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜) :=
      fun _ => inferInstance
    letI : ∀ (x : M), ContinuousSMul 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜) :=
      fun _ => inferInstance
    exact Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜)
      (fun (x : M) => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => CotangentSpace I x) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun (x : M) => ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜)

-- Vector bundle instance for (r,s)-tensors

noncomputable instance tensorRSBundle_vector (r s : ℕ) :
    @VectorBundle
      𝕜
      M
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => CotangentSpace I x) 𝕜 →L[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜)
      _  -- [NontriviallyNormedField 𝕜]
      (fun x => by infer_instance)  -- [∀ x, AddCommMonoid (E x)]
      (fun x => by infer_instance)  -- [∀ x, Module 𝕜 (E x)]
      (tensorRSModel_normedAddCommGroup r s)  -- [NormedAddCommGroup F]
      (tensorRSModel_normedSpace r s)         -- [NormedSpace 𝕜 F]
      _  -- [TopologicalSpace M]
      (tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      _  -- [∀ x, TopologicalSpace (E x)]
      (tensorRSBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      := by
    letI := tensorR0Bundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensorR0Bundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensorR0Bundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI : ∀ (x : M), IsTopologicalAddGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜) :=
      fun _ => inferInstance
    letI : ∀ (x : M), ContinuousSMul 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜) :=
      fun _ => inferInstance
    exact Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜)
      (fun (x : M) => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => CotangentSpace I x) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun (x : M) => ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜)

-- Smooth vector bundle instance for (r,s)-tensors

noncomputable instance tensorRSBundle_smooth (r s : ℕ) :
    @ContMDiffVectorBundle
      n
      𝕜
      M
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => CotangentSpace I x) 𝕜 →L[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜)
      _
      E
      _
      _
      H
      _
      I
      _
      _
      _
      _
      _
      _
      (tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      _
      (tensorRSBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      (tensorRSBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      := by
    letI := tensorR0Bundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensorR0Bundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensorR0Bundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensorR0Bundle_smooth (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_smooth (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI : ∀ (x : M), IsTopologicalAddGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜) :=
      fun _ => inferInstance
    letI : ∀ (x : M), ContinuousSMul 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜) :=
      fun _ => inferInstance
    exact ContMDiffVectorBundle.continuousLinearMap
