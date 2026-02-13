

theorem interior_closure_interior_subset_interior_closure_interior_closure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆
      interior (closure (interior (closure A))) := by
  -- The set `A` is always contained in its closure.
  have hA : (A : Set X) ⊆ closure A := subset_closure
  -- Apply monotonicity of `interior ∘ closure ∘ interior`.
  exact
    Topology.interior_closure_interior_mono
      (X := X) (A := A) (B := closure A) hA