

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro hP2
  dsimp [P2, P3] at *
  intro x hx
  exact (interior_mono (closure_mono (interior_subset))) (hP2 hx)