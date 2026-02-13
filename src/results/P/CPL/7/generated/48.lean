

theorem P3_closed_iff_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    exact open_of_closed_and_P3 hA hP3
  · intro hOpen
    exact P3_of_open hOpen