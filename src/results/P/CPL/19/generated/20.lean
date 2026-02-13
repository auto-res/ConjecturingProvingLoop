

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P1 A := by
  intro hA
  have hP3 : P3 A := P3_of_open (X := X) (A := A) hA
  exact (P1_iff_P3_of_open (X := X) (A := A) hA).2 hP3