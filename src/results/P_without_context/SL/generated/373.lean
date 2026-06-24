

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro h
  dsimp [P2] at h
  dsimp [P1]
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact subset_trans h h₁