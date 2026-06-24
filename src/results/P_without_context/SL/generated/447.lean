

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro hP2
  dsimp [P2, P1] at *
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact hP2.trans h₁