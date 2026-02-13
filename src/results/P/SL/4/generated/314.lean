

theorem frontier_frontier_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (frontier (A : Set X)) ⊆ closure A := by
  intro x hx
  have hx_frontier : x ∈ frontier A :=
    (frontier_frontier_subset_frontier (X := X) (A := A)) hx
  exact (frontier_subset_closure (X := X) (A := A)) hx_frontier