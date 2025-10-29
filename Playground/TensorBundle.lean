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


-- (r,0) tensors
@[simp,reducible]
def TensorR0Space (r : ℕ) (I : ModelWithCorners 𝕜 E H) (x : M) :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin r => CotangentSpace I x) 𝕜


noncomputable def tensorR0_curry
    (r : ℕ) (x : M) :
  TensorR0Space (r+1) I x
    ≃L[𝕜]
  (CotangentSpace I x →L[𝕜] TensorR0Space r I x) := by
  unfold TensorR0Space CotangentSpace
  exact (continuousMultilinearCurryLeftEquiv 𝕜
    (fun _ : Fin (r+1) => E →L[𝕜] 𝕜) 𝕜).toContinuousLinearEquiv


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
      (fun x : M => TensorR0Space 0 I x) :=
     inferInstanceAs <| FiberBundle
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)

noncomputable instance tensorR0_vectorBundle_zero :
    VectorBundle 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => TensorR0Space 0 I x) :=
     inferInstanceAs <| VectorBundle 𝕜
       (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
        (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)


noncomputable instance tensorR0_contMDiffVectorBundle_zero :
    ContMDiffVectorBundle n
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => TensorR0Space 0 I x) I :=
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
      M                                                            -- {B : Type} base
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜) -- (F : Type) model fiber
      _                                                           -- [TopologicalSpace B]
      _                                                           -- [TopologicalSpace F]
      (TensorR0Space r I)                                         -- (E : B → Type) bundle
      (tensorR0Bundle_topology (n := n) r)             -- [TopologicalSpace (TotalSpace F E)]
      _                                               -- [(b : B) → TopologicalSpace (E b)]
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
      _                                                    -- 5. [NontriviallyNormedField R]
      _                                                -- 6. [(x : M) → AddCommMonoid (E x)]
      _                                                     -- 7. [(x : M) → Module R (E x)]
      _                                                         -- 8. [NormedAddCommGroup F]
      _                                                            -- 9. [NormedSpace R F]
      _                                                          -- 10. [TopologicalSpace M]
      (tensorR0Bundle_topology (n := n) r)        -- 11. [TopologicalSpace (TotalSpace F E)]
      _                                            -- 12. [(x : M) → TopologicalSpace (E x)]
      (tensorBundleData n r).fiber                                  -- 13. [FiberBundle F E]
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
      _                                                           -- 6. [NontriviallyNormedField 𝕜]
      E                                                              -- 7. EB: model space for base
      _                                                              -- 8. [NormedAddCommGroup EB]
      _                                                              -- 9. [NormedSpace 𝕜 EB]
      H                                                         -- 10. HB: model topological space
      _                                                              -- 11. [TopologicalSpace HB]
      I                                                              -- 12. IB: model with corners
      _                                                              -- 13. [TopologicalSpace M]
      _                                                              -- 14. [ChartedSpace HB M]
      _                                                     -- 15. [(x : M) → AddCommMonoid (E x)]
      _                                                         -- 16. [(x : M) → Module 𝕜 (E x)]
      _                                                             -- 17. [NormedAddCommGroup F]
      _                                                              -- 18. [NormedSpace 𝕜 F]
      (tensorR0Bundle_topology (n := n) r)             -- 19. [TopologicalSpace (TotalSpace F E)]
      _                                                  -- 20. [(x : M) → TopologicalSpace (E x)]
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

noncomputable instance tensorRSBundle_topology (r s : ℕ) :
    TopologicalSpace (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun x : M => TensorR0Space s I x →L[𝕜] TensorR0Space r I x)) := by

    letI := tensorR0Bundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensorR0Bundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensorR0Bundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r

    exact Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜)
      (fun (x : M) => TensorR0Space s I x)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun (x : M) => TensorR0Space r I x)


-- Fiber bundle instance
noncomputable instance tensorRSBundle_fiber (r s : ℕ) :
    @FiberBundle
      M  -- base space B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)  -- model fiber F
      _  -- [TopologicalSpace B]
      _  -- [TopologicalSpace F]
      (fun x : M => TensorR0Space s I x →L[𝕜] TensorR0Space r I x)  -- bundle E
      (tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
                                                -- [TopologicalSpace (TotalSpace F E)]
      _  -- [∀ x, TopologicalSpace (E x)]
      := by
    letI := tensorR0Bundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensorR0Bundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensorR0Bundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI : ∀ (x : M), IsTopologicalAddGroup (TensorR0Space r I x) := fun _ => inferInstance
    letI : ∀ (x : M), ContinuousSMul 𝕜 (TensorR0Space r I x) := fun _ => inferInstance
    exact Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜)
      (fun (x : M) => TensorR0Space s I x)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun (x : M) => TensorR0Space r I x)

-- Vector bundle instance
set_option maxHeartbeats 800000 in
noncomputable instance tensorRSBundle_vector (r s : ℕ) :
    @VectorBundle
      𝕜  -- field R
      M  -- base space B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)  -- model fiber F
      (fun x : M => TensorR0Space s I x →L[𝕜] TensorR0Space r I x)  -- bundle E
      _  -- [NontriviallyNormedField 𝕜]
      _  -- [∀ x, AddCommMonoid (E x)]
      _  -- [∀ x, Module 𝕜 (E x)]
      _  -- [NormedAddCommGroup F]
      _  -- [NormedSpace 𝕜 F]
      _  -- [TopologicalSpace M]
      (tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)  -- [TopologicalSpace (TotalSpace F E)]
      _  -- [∀ x, TopologicalSpace (E x)]
      (tensorRSBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)  -- [FiberBundle F E]
      := by
    letI := tensorR0Bundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensorR0Bundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensorR0Bundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensorR0Bundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI : ∀ (x : M), IsTopologicalAddGroup (TensorR0Space r I x) := fun _ => inferInstance
    letI : ∀ (x : M), ContinuousSMul 𝕜 (TensorR0Space r I x) := fun _ => inferInstance
    exact Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜)
      (fun (x : M) => TensorR0Space s I x)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)
      (fun (x : M) => TensorR0Space r I x)




-- Main smooth instance

set_option maxHeartbeats 800000 in
noncomputable instance tensorRSBundle_smooth (r s : ℕ) :
    @ContMDiffVectorBundle
      n                                                              -- smoothness degree
      𝕜                                                              -- field
      M                                                              -- base manifold
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E →L[𝕜] 𝕜) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E →L[𝕜] 𝕜) 𝕜)  -- model fiber
      (fun x : M => TensorR0Space s I x →L[𝕜] TensorR0Space r I x)  -- bundle
      _                                                              -- [NontriviallyNormedField 𝕜]
      E                                                              -- EB: model space for base
      _                                                              -- [NormedAddCommGroup EB]
      _                                                              -- [NormedSpace 𝕜 EB]
      H                                                              -- HB: model topological space
      _                                                              -- [TopologicalSpace HB]
      I                                                              -- IB: model with corners
      _                                                              -- [TopologicalSpace M]
      _                                                              -- [ChartedSpace HB M]
      _                                                              -- [∀ x, AddCommMonoid (E x)]
      _                                                              -- [∀ x, Module 𝕜 (E x)]
      _                                                              -- [NormedAddCommGroup F]
      _                                                              -- [NormedSpace 𝕜 F]
      (tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      _                                                              -- [∀ x, TopologicalSpace (E x)]
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
    letI : ∀ (x : M), IsTopologicalAddGroup (TensorR0Space r I x) := fun _ => inferInstance
    letI : ∀ (x : M), ContinuousSMul 𝕜 (TensorR0Space r I x) := fun _ => inferInstance
    -- Use the smooth hom bundle instance
    exact ContMDiffVectorBundle.continuousLinearMap
