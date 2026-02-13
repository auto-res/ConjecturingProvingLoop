

theorem Topology.closure_subset_closure_union_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure A ⊆ closure (A ∪ B) := by
  intro x hx
  have hIncl : (A : Set X) ⊆ A ∪ B := by
    intro y hy
    exact Or.inl hy
  exact (closure_mono hIncl) hx