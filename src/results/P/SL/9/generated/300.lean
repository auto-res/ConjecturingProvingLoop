

theorem Topology.closure_frontier_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier (A : Set X)) ⊆ closure A := by
  -- `frontier A` is contained in `closure A`.
  have h : frontier (A : Set X) ⊆ closure A := by
    intro x hx
    exact hx.1
  -- Taking closures preserves inclusions.
  have h' : closure (frontier (A : Set X)) ⊆ closure (closure A) := closure_mono h
  simpa [closure_closure] using h'