

theorem P3_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    P3 (X := X) (interior (closure (interior A))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact isOpen_implies_P3 (X := X) (A := interior (closure (interior A))) h_open