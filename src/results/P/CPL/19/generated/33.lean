

theorem P3_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior A = Set.univ) : P3 A ↔ P2 A := by
  constructor
  · intro _hP3
    exact P2_of_dense_interior (X := X) (A := A) h
  · intro hP2
    exact P2_subset_P3 (X := X) (A := A) hP2