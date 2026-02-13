

theorem P2_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : interior A = Set.univ → (P2 A ↔ P3 A) := by
  intro hInt
  constructor
  · intro hP2
    exact (P2_imp_P3 (A := A)) hP2
  · intro _hP3
    exact (P2_of_dense_interior (A := A)) hInt