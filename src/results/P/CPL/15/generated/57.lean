

theorem P2_exists_dense_subset {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : ∃ B, B ⊆ A ∧ closure (interior B) = closure (interior A) := by
  refine ⟨interior A, interior_subset, ?_⟩
  simpa [interior_interior]