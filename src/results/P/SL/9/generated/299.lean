

theorem Topology.frontier_closureInterior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (closure (interior (A : Set X))) ⊆ frontier A := by
  -- `frontier (closure (interior A)) ⊆ frontier (interior A)`
  have h₁ :
      frontier (closure (interior (A : Set X))) ⊆
        frontier (interior (A : Set X)) :=
    Topology.frontier_closure_subset_frontier (A := interior A)
  -- `frontier (interior A) ⊆ frontier A`
  have h₂ :
      frontier (interior (A : Set X)) ⊆ frontier A :=
    Topology.frontier_interior_subset_frontier (A := A)
  -- Combine the two inclusions.
  exact subset_trans h₁ h₂