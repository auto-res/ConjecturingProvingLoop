

theorem Topology.closure_subset_closure_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (B : Set X) ⊆ closure (A ∪ B) := by
  have h_subset : (B : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inr hx
  exact closure_mono h_subset