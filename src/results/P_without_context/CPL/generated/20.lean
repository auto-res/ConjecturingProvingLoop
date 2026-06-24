

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P3 A := by
  exact
    hA.trans
      (interior_mono
        (closure_mono interior_subset))

theorem subset_interior_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : interior A ⊆ interior (closure A) := by
  exact interior_subset.trans (P3_of_P2 hA)

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  dsimp [P1]
  simpa [interior_interior] using
    (subset_closure : interior A ⊆ closure (interior A))

theorem exists_nontrivial_P2 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, P2 A ∧ A.Nonempty := by
  classical
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · dsimp [P2]
    simpa [interior_univ, closure_univ] using
      (subset_rfl : (Set.univ : Set X) ⊆ Set.univ)
  · exact ⟨Classical.arbitrary X, by simp⟩