

theorem P2_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P2 (closure A) := by
  exact
    (Topology.isOpen_implies_P2
        (X := X)
        (A := closure (A : Set X))) hOpen