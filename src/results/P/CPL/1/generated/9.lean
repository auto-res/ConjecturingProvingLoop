

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure A = (⊤ : Set X)) : P3 A := by
  intro x hx
  simpa [hA, interior_univ] using (by
    simp : x ∈ (⊤ : Set X))

theorem exists_P3_dense {X : Type*} [TopologicalSpace X] : ∃ A : Set X, P3 A ∧ closure A = (⊤ : Set X) := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact P3_univ
  · simpa [closure_univ]