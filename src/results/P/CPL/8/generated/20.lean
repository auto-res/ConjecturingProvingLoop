

theorem P3_closed_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P2 A → P3 A := by
  intro _ hP2
  exact P2_to_P3 (A := A) hP2