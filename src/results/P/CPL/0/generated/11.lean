

theorem exists_min_P3_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B : Set X, B ⊆ A ∧ P3 B ∧ (∀ C : Set X, C ⊆ B → P3 C → C = B) := by
  refine ⟨(∅ : Set X), ?_, ?_, ?_⟩
  · intro x hx
    cases hx
  · intro x hx
    cases hx
  · intro C hCsubset _hP3C
    apply Set.Subset.antisymm hCsubset
    exact Set.empty_subset _