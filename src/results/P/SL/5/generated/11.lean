

theorem isOpen_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : P1 (X := X) A := by
  have hP2 : P2 (X := X) A := isOpen_implies_P2 (X := X) (A := A) hA
  exact P2_implies_P1 (X := X) (A := A) hP2