

theorem exists_P3_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ P3 B := by
  refine ⟨(∅ : Set X), Set.empty_subset _, ?_⟩
  have h : P3 (∅ : Set X) := (P2_imp_P3 (∅ : Set X)) P2_empty
  simpa using h