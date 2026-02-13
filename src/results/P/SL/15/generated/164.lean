

theorem interior_has_all_P {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) ∧
      Topology.P2 (interior A) ∧
        Topology.P3 (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  exact
    Topology.isOpen_has_all_P
      (X := X) (A := interior A) h_open