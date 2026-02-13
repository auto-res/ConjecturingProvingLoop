

theorem isOpen_implies_all_P123 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    P1 (X := X) A ∧ P2 (X := X) A ∧ P3 (X := X) A := by
  exact
    ⟨isOpen_implies_P1 (X := X) (A := A) hA,
     isOpen_implies_P2 (X := X) (A := A) hA,
     isOpen_implies_P3 (X := X) (A := A) hA⟩