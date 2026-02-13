

theorem Topology.interiorClosure_subset_interiorClosure_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (B : Set X)) ⊆ interior (closure (A ∪ B)) := by
  have h_subset : (B : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inr hx
  exact Topology.interiorClosure_mono (X := X) (A := B) (B := A ∪ B) h_subset