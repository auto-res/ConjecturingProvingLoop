

theorem Topology.closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  -- We have the obvious inclusion `A ⊆ closure A`.
  have h_subset : A ⊆ closure A := subset_closure
  -- Apply the monotonicity of the `closure ∘ interior` operator.
  simpa using
    (Topology.closure_interior_mono (X := X) (A := A) (B := closure A) h_subset)