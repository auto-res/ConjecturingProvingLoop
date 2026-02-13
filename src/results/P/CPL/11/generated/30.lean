

theorem exists_closed_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ C, IsClosed C ∧ C ⊆ A := by
  refine ⟨(∅ : Set X), isClosed_empty, ?_⟩
  intro x hx
  cases hx