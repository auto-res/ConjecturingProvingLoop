

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro hA
  dsimp [P2, P3] at *
  have hsub : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact subset_trans hA hsub