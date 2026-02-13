

theorem frontier_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (closure (A : Set X)) ⊆ closure A := by
  have h₁ :
      frontier (closure (A : Set X)) ⊆ frontier (A : Set X) :=
    Topology.frontier_closure_subset_frontier (A := A)
  have h₂ :
      frontier (A : Set X) ⊆ closure A :=
    Topology.frontier_subset_closure (A := A)
  exact Set.Subset.trans h₁ h₂