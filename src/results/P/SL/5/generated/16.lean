

theorem P1_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    P1 (X := X) (interior A) := by
  have hP2 : P2 (X := X) (interior A) := P2_interior (X := X) A
  exact P2_implies_P1 (X := X) (A := interior A) hP2