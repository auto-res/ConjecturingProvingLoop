

theorem Topology.closure_interior_closure_subset_self_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) :
    closure (interior (closure A)) ⊆ A := by
  -- `interior (closure A)` is contained in `closure A`.
  have h₁ : interior (closure A) ⊆ closure A := interior_subset
  -- Taking closures preserves inclusions.
  have h₂ : closure (interior (closure A)) ⊆ closure (closure A) :=
    closure_mono h₁
  -- Since `A` is closed, its closure is itself, and `closure (closure A)` simplifies.
  simpa [closure_closure, hClosed.closure_eq] using h₂