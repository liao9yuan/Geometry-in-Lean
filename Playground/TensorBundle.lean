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
Construct Cotangent Bundle v
Construct (n,0) tensors v
Construct (n,k) tensors v
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
    NormedAddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜) :=
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

noncomputable instance tensorBundleData : (r : ℕ) →
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

@[simp, reducible]
noncomputable instance tensorR0Bundle_fiber (r : ℕ) :
    @FiberBundle
      M                                                              -- {B : Type} base
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜) -- (F : Type) model fiber
      _                                                              -- [TopologicalSpace B]
      _                                                              -- [TopologicalSpace F]
      (TensorR0Space r I)                                            -- (E : B → Type) bundle
      (tensorR0Bundle_topology (n := n) r)                           -- [TopologicalSpace (TotalSpace F E)]
      _                                                              -- [(b : B) → TopologicalSpace (E b)]
      :=
  (@tensorBundleData 𝕜 _ E _ _ _ H _ I M _ _ n _ r).fiber


-- Vector bundle instance with explicit topology
@[simp]
noncomputable instance tensorR0Bundle_vector (r : ℕ) :
    @VectorBundle
      𝕜                                                              -- 1. R: field
      M                                                              -- 2. B: base manifold
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜) -- 3. F: model fiber
      (TensorR0Space r I)                                            -- 4. E: bundle
      _                                                              -- 5. [NontriviallyNormedField R]
      _                                                              -- 6. [(x : M) → AddCommMonoid (E x)]
      _                                                              -- 7. [(x : M) → Module R (E x)]
      _                                                              -- 8. [NormedAddCommGroup F]
      _                                                              -- 9. [NormedSpace R F]
      _                                                              -- 10. [TopologicalSpace M]
      (tensorR0Bundle_topology (n := n) r)                           -- 11. [TopologicalSpace (TotalSpace F E)] ← KEY!
      _                                                              -- 12. [(x : M) → TopologicalSpace (E x)]
      (tensorBundleData n r).fiber                                   -- 13. [FiberBundle F E]
      :=
  (tensorBundleData (n := n) r).vector

@[simp]
noncomputable instance tensorR0Bundle_smooth (r : ℕ) :
    @ContMDiffVectorBundle
      n                                                              -- 1. n: smoothness degree
      𝕜                                                              -- 2. 𝕜: field
      M                                                              -- 3. B: base manifold
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)   -- 4. F: model fiber
      (TensorR0Space r I)                                            -- 5. E: bundle
      _                                                              -- 6. [NontriviallyNormedField 𝕜]
      E                                                              -- 7. EB: model space for base
      _                                                              -- 8. [NormedAddCommGroup EB]
      _                                                              -- 9. [NormedSpace 𝕜 EB]
      H                                                              -- 10. HB: model topological space
      _                                                              -- 11. [TopologicalSpace HB]
      I                                                              -- 12. IB: model with corners
      _                                                              -- 13. [TopologicalSpace M]
      _                                                              -- 14. [ChartedSpace HB M]
      _                                                              -- 15. [(x : M) → AddCommMonoid (E x)]
      _                                                              -- 16. [(x : M) → Module 𝕜 (E x)]
      _                                                              -- 17. [NormedAddCommGroup F]
      _                                                              -- 18. [NormedSpace 𝕜 F]
      (tensorR0Bundle_topology (n := n) r)                           -- 19. [TopologicalSpace (TotalSpace F E)] ← KEY!
      _                                                              -- 20. [(x : M) → TopologicalSpace (E x)]
      (tensorBundleData n r).fiber                                   -- 21. [FiberBundle F E]
      (tensorBundleData n r).vector                                  -- 22. [VectorBundle 𝕜 F E]
      :=
  (tensorBundleData (n := n) r).smooth

#check tensorR0Bundle_smooth n 5

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


noncomputable def tensorRSBundle_smooth_def (r s : ℕ) :=
  @ContMDiffVectorBundle.continuousLinearMap
      𝕜 M
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜)  -- s is source
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)  -- r is target
      n
      (TensorR0Space (I := I) (M := M) s)  -- s is source (E₁)
      (TensorR0Space (I := I) (M := M) r)  -- r is target (E₂)
      _ _ _ _ _
      (@tensorR0Bundle_topology 𝕜 _ E _ _ _ H _ I M _ _ n _ s)  -- source topology
      _ _ _ _ _
      (@tensorR0Bundle_topology 𝕜 _ E _ _ _ H _ I M _ _ n _ r)  -- target topology
      _
      E _ _ H _ I _ _
      ((@tensorBundleData 𝕜 _ E _ _ _ H _ I M _ _ n _ s).fiber)   -- source fiber
      ((@tensorBundleData 𝕜 _ E _ _ _ H _ I M _ _ n _ s).vector)  -- source vector
      ((@tensorBundleData 𝕜 _ E _ _ _ H _ I M _ _ n _ r).fiber)   -- target fiber
      ((@tensorBundleData 𝕜 _ E _ _ _ H _ I M _ _ n _ r).vector)  -- target vector
      _ _
      (@tensorR0Bundle_smooth 𝕜 _ E _ _ _ H _ I M _ _ n _ s)      -- source smooth
      (@tensorR0Bundle_smooth 𝕜 _ E _ _ _ H _ I M _ _ n _ r)      -- target smooth

#check tensorRSBundle_smooth_def n 5 6


-- Topology instance with explicit parameters in header
-- Adapt the topology construction from the hom bundle file with all parameters explicit
noncomputable instance tensorRSBundle_topology_inst (r s : ℕ) :
    @TopologicalSpace
      (TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
         ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
        (fun x : M => TensorR0Space s I x →L[𝕜] TensorR0Space r I x)) :=
  @TopologicalSpace.induced
    (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => TensorR0Space s I x →L[𝕜] TensorR0Space r I x))
    (M × (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
          ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜))
    (fun p => (p.proj, p.2))
    (by letI := @tensorR0Bundle_topology 𝕜 _ E _ _ _ H _ I M _ _ n _ s
        letI := @tensorR0Bundle_topology 𝕜 _ E _ _ _ H _ I M _ _ n _ r
        exact inferInstance)

-- Instance for fiber-wise topology
noncomputable instance tensorRSBundle_fiber_topology (r s : ℕ) (b : M) :
    TopologicalSpace (TensorR0Space s I b →L[𝕜] TensorR0Space r I b) := by
  letI := @tensorR0Bundle_topology 𝕜 _ E _ _ _ H _ I M _ _ n _ s
  letI := @tensorR0Bundle_topology 𝕜 _ E _ _ _ H _ I M _ _ n _ r
  exact inferInstance


noncomputable instance tensorRSBundle_fiber_inst (r s : ℕ) :
    FiberBundle
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => TensorR0Space s I x →L[𝕜] TensorR0Space r I x) :=

      sorry

noncomputable instance tensorRSBundle_vector_inst (r s : ℕ) :
    VectorBundle 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => TensorR0Space s I x →L[𝕜] TensorR0Space r I x) :=
      sorry


-- Main smooth instance
noncomputable instance tensorRSBundle_smooth (r s : ℕ) :
    @ContMDiffVectorBundle
      n                                                              -- 1. n: smoothness degree
      𝕜                                                              -- 2. 𝕜: field
      M                                                              -- 3. B: base manifold
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜) -- 4. F: model fiber (hom type)
      (fun x : M => TensorR0Space s I x →L[𝕜] TensorR0Space r I x) -- 5. E: bundle (hom bundle)
      _                                                              -- 6. [NontriviallyNormedField 𝕜]
      E                                                              -- 7. EB: model space for base
      _                                                              -- 8. [NormedAddCommGroup EB]
      _                                                              -- 9. [NormedSpace 𝕜 EB]
      H                                                              -- 10. HB: model topological space
      _                                                              -- 11. [TopologicalSpace HB]
      I                                                              -- 12. IB: model with corners
      _                                                              -- 13. [TopologicalSpace M]
      _                                                              -- 14. [ChartedSpace HB M]
      _                                                              -- 15. [(x : M) → AddCommMonoid (E x)]
      _                                                              -- 16. [(x : M) → Module 𝕜 (E x)]
      _                                                              -- 17. [NormedAddCommGroup F]
      _                                                              -- 18. [NormedSpace 𝕜 F]
      _
      _                                                              -- 20. [(x : M) → TopologicalSpace (E x)]
      _
      (by apply tensorRSBundle_vector_inst)
      := by
        have h1 := tensorR0Bundle_smooth (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
        have h2 := tensorR0Bundle_smooth (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s

        apply ContMDiffVectorBundle.continuousLinearMap


noncomputable instance tensorRSBundle_smooth' (r s : ℕ) :
    ContMDiffVectorBundle n
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => TensorR0Space s I x →L[𝕜] TensorR0Space r I x) I :=
  ContMDiffVectorBundle.continuousLinearMap
