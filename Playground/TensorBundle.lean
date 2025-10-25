/- This file defines tensor bundle on a smooth manifold by the follwoing

Let `M` be a manifold with model `I` on `(E, H),` whereas we assumed that `M` has finite dimension
The tangent space `TangentSpace I (x : M)` has already been defined as a type synonym for `E`,
and the tangent bundle `TangentBundle I M` as an abbrev of `Bundle.TotalSpace E (TangentSpace I : M → Type _)`.

The cotangent space `CotangentSpace I (x : M)` is the dual TangentSpace I x →L[𝕜] 𝕜
  TangentSpace I x →L[𝕜] 𝕜



To do:
Construct Cotangent Bundle v
Construct (n,0) tensors
Construct (n,k) tensors
Einstein convention/ Frame Bundle?
Lie Derivative
-/


import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Topology.FiberBundle.Basic

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




abbrev CotangentBundle :=
  Bundle.TotalSpace (E →L[𝕜] 𝕜) (CotangentSpace I: M → Type _)




  -- noncomputable instance :
  --     IsManifold (I.prod (𝓘(𝕜, E →L[𝕜] 𝕜))) ω (CotangentBundle (I:=I) (M:=M)) := by
  --   infer_instance

/- abbrev Tensor11 (x : M) := TM I x →L[𝕜] TM I x -/

-- (r,0) tensors
@[simp,reducible]
def TensorR0Space (r : ℕ) (I : ModelWithCorners 𝕜 E H) (x : M) :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜



/-Below a few instances were created to avoid diamond problem-/
instance (r : ℕ) (x : M) :
    TopologicalSpace (CotangentSpace I x →L[𝕜] TensorR0Space r I x) :=
  @ContinuousLinearMap.topologicalSpace 𝕜 𝕜 _ _ (RingHom.id 𝕜)
    (CotangentSpace I x) (TensorR0Space r I x) _ _ _ _ _ _ _


noncomputable instance (r : ℕ) (x : M) :
    NormedAddCommGroup (CotangentSpace I x →L[𝕜] TensorR0Space r I x) :=
  @ContinuousLinearMap.toNormedAddCommGroup 𝕜 𝕜
    (CotangentSpace I x) (TensorR0Space r I x)
    _ _ _ _ _ _
    (RingHom.id 𝕜)
    _ -- RingHomIsometric

noncomputable instance (r : ℕ) :
    TopologicalSpace ((E →L[𝕜] 𝕜) →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜) :=
  @ContinuousLinearMap.topologicalSpace 𝕜 𝕜 _ _ (RingHom.id 𝕜)
    (E →L[𝕜] 𝕜) (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
    _ _ _ _ _ _ _


noncomputable instance (r : ℕ) :
    NormedAddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜) :=
  @ContinuousLinearMap.toNormedAddCommGroup 𝕜 𝕜
    (E →L[𝕜] 𝕜) (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id 𝕜)
    inferInstance
/-End of section to establish instance inference-/


noncomputable def tensorR0_curry
    (r : ℕ) (x : M):
  TensorR0Space (r+1) I x
    ≃L[𝕜]
  (CotangentSpace I x →L[𝕜] TensorR0Space r I x) := by
  unfold TensorR0Space CotangentSpace
  exact (continuousMultilinearCurryLeftEquiv 𝕜
    (fun _ : Fin (r+1) => E →L[𝕜] 𝕜) 𝕜).toContinuousLinearEquiv

#check TensorR0Space 0 I x'
#reduce TensorR0Space 0 I x'


#check Bundle.Trivial
#synth ContMDiffVectorBundle n 𝕜 (fun x : M => 𝕜) I


-- noncomputable def tensorR0Space_zero_to_scalar :
--     ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜 ≃L[𝕜] 𝕜 :=
--   (continuousMultilinearCurryFin0 𝕜 (E →L[𝕜] 𝕜) 𝕜).toContinuousLinearEquiv


-- example (x y : M) : TensorR0Space 0 I x = TensorR0Space 0 I y := by
--   unfold TensorR0Space CotangentSpace
--   rfl


-- noncomputable instance tensorR0_zero_bundle :
--     ContMDiffVectorBundle n
--       (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
--       (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜) I := by
--   apply Bundle.Trivial.contMDiffVectorBundle


@[simp, reducible]
def TensorR0Space' : (r : ℕ) → (I : ModelWithCorners 𝕜 E H) → (x : M) → Type _
  | 0, _, _ => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜
  | r + 1, I, x => ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + 1) => CotangentSpace I x) 𝕜
-- Inductive step: Hom(Cotangent, TensorR0Space r)

noncomputable instance tensorR0_topologicalSpace_zero :
    TopologicalSpace (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => TensorR0Space 0 I x)) := by
  have h : (fun x : M => TensorR0Space 0 I x) =
           (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜) := by
    ext x
    unfold TensorR0Space CotangentSpace
    rfl
  rw [h]
  infer_instance

noncomputable instance tensorR0_fiberBundle_zero :
    FiberBundle
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => TensorR0Space 0 I x) := by
  convert (inferInstance : FiberBundle
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
    (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)) using 2

noncomputable instance tensorR0_vectorBundle_zero :
    VectorBundle 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => TensorR0Space 0 I x) := by
  convert (inferInstance : VectorBundle 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
    (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)) using 2


noncomputable instance tensorR0_contMDiffVectorBundle_zero :
    ContMDiffVectorBundle n
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => TensorR0Space 0 I x) I := by
    convert (inferInstance : ContMDiffVectorBundle n
       (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
       (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜) I) using 3





structure TensorBundleData (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (H : Type*) [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (n : WithTop ℕ∞) [IsManifold I n M]
    (r : ℕ) where
  topology : TopologicalSpace (TotalSpace
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
    (fun x : M => TensorR0Space r I x))
  fiber : FiberBundle
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
    (fun x : M => TensorR0Space r I x)
  vector : VectorBundle 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
    (fun x : M => TensorR0Space r I x)
  smooth : ContMDiffVectorBundle n
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
    (fun x : M => TensorR0Space r I x) I



noncomputable def tensorBundleData_zero :
    TensorBundleData (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) 0 := {
  topology := tensorR0_topologicalSpace_zero
  fiber := tensorR0_fiberBundle_zero
  vector := tensorR0_vectorBundle_zero
  smooth := by
    convert (inferInstance : ContMDiffVectorBundle n
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜) I) using 2
}

noncomputable def tensorBundleData : (r : ℕ) →
    TensorBundleData (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
  | 0 => tensorBundleData_zero  (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n)
  | r + 1 => by
    -- Get the bundle data for rank r by induction
    let prev := tensorBundleData r

    -- Build rank (r+1) as Hom(Cotangent, TensorR0Space r)
    refine {
      topology := ?_,
      fiber := ?_,
      vector := ?_,
      smooth := ?_
    }

    -- Topology
    · have h : (fun x : M => TensorR0Space (r+1) I x) =
              (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin (r+1) => E →L[𝕜] 𝕜) 𝕜) := by
        ext x
        unfold TensorR0Space CotangentSpace
        rfl
      rw [h]
      infer_instance
    -- Fiber bundle
    · convert (inferInstance : FiberBundle
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (r+1) => E →L[𝕜] 𝕜) 𝕜)
        (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin (r+1) => E →L[𝕜] 𝕜) 𝕜)) using 3

    -- Vector bundle
    · convert (inferInstance : VectorBundle 𝕜
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (r+1) => E →L[𝕜] 𝕜) 𝕜)
        (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin (r+1) => E →L[𝕜] 𝕜) 𝕜)) using 2

    -- Smooth vector bundle
    · haveI : ContMDiffVectorBundle n (E →L[𝕜] 𝕜)
        (fun x : M => CotangentSpace I x) I := inferInstance
      convert (inferInstance : ContMDiffVectorBundle n
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (r+1) => E →L[𝕜] 𝕜) 𝕜)
        (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin (r+1) => E →L[𝕜] 𝕜) 𝕜) I) using 3



@[reducible]
def TensorR0Bundle
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (H : Type*) [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (r : ℕ) :=
  Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
    (TensorR0Space r I : M → Type _)

instance tensorR0Bundle_topology (r : ℕ) :
    TopologicalSpace (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (TensorR0Space r I : M → Type _)) :=
  (tensorBundleData n r).topology





/-temp 3-/

variable [∀ r, TopologicalSpace (TotalSpace
  (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
  (TensorR0Space r I : M → Type _))]

variable [∀ r, FiberBundle
  (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
  (TensorR0Space r I : M → Type _)]

variable [∀ r, VectorBundle 𝕜
  (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
  (TensorR0Space r I : M → Type _)]

variable [∀ r, ContMDiffVectorBundle n
  (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
  (TensorR0Space r I : M → Type _) I]


@[simp, reducible]
def TensorRSSpace (r s : ℕ) (I : ModelWithCorners 𝕜 E H) (x : M) :=
  TensorR0Space s I x →L[𝕜] TensorR0Space r I x

-- The model fiber
abbrev TensorRSModel (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (r s : ℕ) :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
  ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜

-- Since Mathlib already has Hom bundle infrastructure, this should just work!
@[reducible]
def TensorRSBundle
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (H : Type*) [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (r : ℕ)
    (s : ℕ) :=
  Bundle.TotalSpace (TensorRSModel 𝕜 E r s) (TensorRSSpace r s I : M → Type _)



-- The bundle structure should come for free from Mathlib's Hom bundle
variable (r s : ℕ)
#check (tensorBundleData (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r).smooth

set_option maxHeartbeats 800000 in
noncomputable instance tensorRSBundle_smooth (r s : ℕ) :
    ContMDiffVectorBundle n
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => TensorR0Space s I x →L[𝕜] TensorR0Space r I x) I :=
  ContMDiffVectorBundle.continuousLinearMap


#check tensorRSBundle_smooth 5 6


set_option maxHeartbeats 800000 in
#synth ContMDiffVectorBundle n
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 5 => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin 6 => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => TensorR0Space 5 I x →L[𝕜] TensorR0Space 6 I x) I
