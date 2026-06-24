

theorem P2_imp_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A ∧ P3 A := by
  intro hP2
  have hP1 : P1 A := by
    dsimp [P1]
    intro x hxA
    have hx : x ∈ interior (closure (interior A)) := by
      dsimp [P2] at hP2
      exact hP2 hxA
    exact (interior_subset : interior (closure (interior A)) ⊆ _) hx
  have hP3 : P3 A := by
    dsimp [P3]
    intro x hxA
    have hx : x ∈ interior (closure (interior A)) := by
      dsimp [P2] at hP2
      exact hP2 hxA
    have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
      apply interior_mono
      have : closure (interior A) ⊆ closure A := by
        apply closure_mono
        exact (interior_subset : interior A ⊆ A)
      exact this
    exact hsubset hx
  exact And.intro hP1 hP3