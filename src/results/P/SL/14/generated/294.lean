

theorem Topology.interior_subset_interior_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (B : Set X) ⊆ interior (A ∪ B) := by
  have h_subset : (B : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inr hx
  exact interior_mono h_subset