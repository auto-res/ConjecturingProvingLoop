

theorem P2_of_P3_and_closed {X : Type*} [TopologicalSpace X] {A : Set X} (h_closed : IsClosed A) : P3 A → P2 A := by
  exact (P3_iff_P2_of_closed (X := X) (A := A) h_closed).1