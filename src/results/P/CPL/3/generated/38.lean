

theorem P1_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen A) : P1 A ↔ P2 A := by
  constructor
  · intro _hP1
    exact P2_open h_open
  · intro _hP2
    exact P1_open h_open