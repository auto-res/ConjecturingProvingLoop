

theorem Topology.interior_subset_interior_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ⊆ interior (A ∪ B) := by
  have h_subset : (A : Set X) ⊆ (A ∪ B) := by
    intro x hx
    exact Or.inl hx
  exact interior_mono h_subset