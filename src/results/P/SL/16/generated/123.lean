

theorem Topology.closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  -- `interior (closure A)` is clearly contained in `closure A`.
  have h₁ : interior (closure A) ⊆ closure A := interior_subset
  -- Taking closures preserves this inclusion.
  have h₂ : closure (interior (closure A)) ⊆ closure (closure A) :=
    closure_mono h₁
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using h₂