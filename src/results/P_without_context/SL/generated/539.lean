

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A) → P3 (A) := by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P3]
  have h_sub : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure : closure (interior A) ⊆ closure A := by
      have h_int : interior A ⊆ A := interior_subset
      exact closure_mono h_int
    exact interior_mono h_closure
  exact hP2.trans h_sub