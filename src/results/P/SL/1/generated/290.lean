

theorem Topology.closure_diff_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} : closure (A \ B) ⊆ closure A := by
  intro x hx
  have hsubset : (A \ B : Set X) ⊆ A := by
    intro y hy
    exact hy.1
  exact (closure_mono hsubset) hx