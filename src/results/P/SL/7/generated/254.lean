

theorem Topology.closure_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B : Set X) ⊆ closure (A : Set X) := by
  exact closure_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)