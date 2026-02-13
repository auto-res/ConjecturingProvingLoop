

theorem interior_closure_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  have h₁ : interior A ⊆ A := interior_subset
  have h₂ : closure (interior A) ⊆ closure A := closure_mono h₁
  exact interior_mono h₂