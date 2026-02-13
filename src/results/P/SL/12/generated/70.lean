

theorem Topology.closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (A : Set X))) ⊆ closure A := by
  -- `interior (closure A)` is contained in `closure A`.
  have h₁ :
      (interior (closure (A : Set X)) : Set X) ⊆ closure A :=
    interior_subset
  -- Taking closures preserves the inclusion.
  have h₂ :
      closure (interior (closure (A : Set X))) ⊆ closure (closure A) :=
    closure_mono h₁
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using h₂