

theorem exists_set_with_all_P [Nonempty X] : ∃ A : Set X, P1 A ∧ P2 A ∧ P3 A := by
  -- Obtain a set satisfying `P2`
  rcases exists_set_with_P2 (X := X) with ⟨A, hP2⟩
  exact ⟨A, P1_of_P2 hP2, hP2, P3_of_P2 hP2⟩