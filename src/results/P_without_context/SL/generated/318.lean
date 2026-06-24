

theorem P2_imp_P1_and_P3 {A : Set X} :
    P2 A → (P1 A ∧ P3 A) := by
  intro hP2
  -- Rewrite `hP2` into a subset statement
  have hP2' : A ⊆ interior (closure (interior A)) := by
    simpa [P2] using hP2
  -- Proof of `P1 A`
  have hP1 : P1 A := by
    have h : A ⊆ closure (interior A) := hP2'.trans interior_subset
    simpa [P1] using h
  -- Proof of `P3 A`
  have hP3 : P3 A := by
    have hsub : interior (closure (interior A)) ⊆ interior (closure A) := by
      have h : closure (interior A) ⊆ closure A := closure_mono interior_subset
      exact interior_mono h
    have h : A ⊆ interior (closure A) := hP2'.trans hsub
    simpa [P3] using h
  exact And.intro hP1 hP3