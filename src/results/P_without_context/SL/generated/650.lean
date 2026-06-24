

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro hA
  dsimp [P2] at hA
  dsimp [P3]
  have h1 : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have h2 : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h1
  exact subset_trans hA h2