

theorem interior_closure_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ⊆ interior (closure (A ∪ B)) := by
  have h_closure : closure A ⊆ closure (A ∪ B) := by
    have h_subset : A ⊆ A ∪ B := by
      intro x hx
      exact Or.inl hx
    exact closure_mono h_subset
  exact interior_mono h_closure