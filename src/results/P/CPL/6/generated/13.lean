

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P2 A := by
  constructor
  · intro _; exact P2_of_open (A := A) hA
  · intro hP2; exact P2_implies_P1 (A := A) hP2