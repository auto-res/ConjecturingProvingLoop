

theorem Topology.closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  -- First, `interior (closure A)` is contained in `closure A`.
  have h : interior (closure A) ⊆ closure A := interior_subset
  -- Taking closures preserves inclusions; simplify `closure (closure A)`.
  simpa [closure_closure] using closure_mono h