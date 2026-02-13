

theorem P2_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    P2 (X := X) (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  exact isOpen_implies_P2 (X := X) (A := interior (closure A)) h_open