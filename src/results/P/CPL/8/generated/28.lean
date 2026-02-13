

theorem P3_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A ↔ P2 A := by
  simpa using
    ((P3_iff_P1_of_open (A := A) hA).trans (P1_iff_P2_of_open (A := A) hA))