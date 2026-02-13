

theorem P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    P2 (X := X) (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  exact isOpen_implies_P2 (X := X) (A := interior A) h_open