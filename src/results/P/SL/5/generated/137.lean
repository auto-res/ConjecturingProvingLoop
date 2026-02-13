

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : P2 (X := X) A) :
    P1 (X := X) A ∧ P3 (X := X) A := by
  exact ⟨P2_implies_P1 (X := X) (A := A) hP2,
        P2_implies_P3 (X := X) (A := A) hP2⟩