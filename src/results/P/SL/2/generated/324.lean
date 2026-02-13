

theorem Topology.closure_frontier_frontier_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (frontier (frontier (A : Set X))) ⊆ closure (A : Set X) := by
  -- `frontier (frontier A)` is contained in `closure (frontier A)`.
  have h₁ :
      (frontier (frontier (A : Set X)) : Set X) ⊆
        closure (frontier (A : Set X)) :=
    Topology.frontier_subset_closure (A := frontier (A : Set X))
  -- `closure (frontier A)` is contained in `closure A`.
  have h₂ :
      (closure (frontier (A : Set X)) : Set X) ⊆
        closure (A : Set X) :=
    Topology.closure_frontier_subset_closure (A := A)
  -- Compose the inclusions and take closures.
  have h₃ :
      (frontier (frontier (A : Set X)) : Set X) ⊆
        closure (A : Set X) :=
    h₁.trans h₂
  simpa [closure_closure] using closure_mono h₃