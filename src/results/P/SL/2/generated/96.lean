

theorem Topology.closure_interior_closure_subset_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (A : Set X))) ⊆ closure A := by
  -- `interior (closure A)` is contained in `closure A`
  have h : (interior (closure (A : Set X)) : Set X) ⊆ closure A :=
    interior_subset
  -- Taking closures preserves inclusions; simplify with `closure_closure`
  simpa [closure_closure] using closure_mono h