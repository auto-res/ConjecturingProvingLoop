

theorem P2_imp_P1_and_P3 {A : Set X} (h : P2 (A := A)) :
    P1 (A := A) ∧ P3 (A := A) := by
  have hP1 : P1 (A := A) := by
    dsimp [P1, P2] at h ⊢
    exact Set.Subset.trans h interior_subset
  have hP3 : P3 (A := A) := by
    dsimp [P3, P2] at h ⊢
    have h_ic_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
      have h_closure_subset : closure (interior A) ⊆ closure A :=
        closure_mono interior_subset
      exact interior_mono h_closure_subset
    exact Set.Subset.trans h h_ic_subset
  exact And.intro hP1 hP3