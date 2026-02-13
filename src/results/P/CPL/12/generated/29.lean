

theorem P1_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 A → P1 A := by
  intro hP3
  have hP2 : P2 A := (P2_iff_P3_of_closed hA).mpr hP3
  exact P1_of_P2 hP2