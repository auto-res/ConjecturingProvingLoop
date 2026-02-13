

theorem exists_min_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ P1 B ∧ (∀ C, C ⊆ B → P1 C → C = B) := by
  refine ⟨(∅ : Set X), Set.empty_subset _, P1_empty, ?_⟩
  intro C hCsubset _hP1C
  exact subset_antisymm hCsubset (Set.empty_subset _)