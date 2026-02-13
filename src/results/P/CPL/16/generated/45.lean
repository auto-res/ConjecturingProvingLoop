

theorem P3_of_P2_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P2 A → P3 A := by
  intro hClosed hP2
  exact ((P2_iff_P3_of_closed (A := A) hClosed).1 hP2)