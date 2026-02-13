

theorem Topology.interiorClosure_subset_interiorClosure_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X)) ⊆ interior (closure (A ∪ B)) := by
  have h_subset : (A : Set X) ⊆ (A ∪ B) := by
    intro x hx
    exact Or.inl hx
  exact
    Topology.interiorClosure_mono (X := X) (A := A) (B := A ∪ B) h_subset