

theorem P2_imp_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A ∧ P3 A := by
  intro hP2
  -- first, deduce P1
  have hP1 : P1 A := by
    dsimp [P1, P2] at *
    exact Set.Subset.trans hP2 interior_subset
  -- next, deduce P3
  have hP3 : P3 A := by
    dsimp [P3, P2] at *
    have h_closure : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    have h_int : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono h_closure
    exact Set.Subset.trans hP2 h_int
  exact And.intro hP1 hP3