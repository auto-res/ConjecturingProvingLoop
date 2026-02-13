

theorem Topology.closure_frontier_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier (A : Set X)) ⊆ closure (A : Set X) := by
  -- First, we recall the inclusion `frontier A ⊆ closure A`.
  have h : (frontier (A : Set X) : Set X) ⊆ closure (A : Set X) :=
    Topology.frontier_subset_closure (A := A)
  -- Taking closures preserves inclusions; simplify with `closure_closure`.
  simpa [closure_closure] using closure_mono h