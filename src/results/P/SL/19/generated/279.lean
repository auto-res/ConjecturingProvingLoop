

theorem Topology.frontier_subset_of_closure_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h : closure A ⊆ B) :
    frontier A ⊆ B := by
  intro x hx
  exact h hx.1