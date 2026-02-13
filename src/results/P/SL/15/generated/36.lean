

theorem interior_closure_interior_has_all_P {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (interior A))) ∧
      Topology.P2 (interior (closure (interior A))) ∧
        Topology.P3 (interior (closure (interior A))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact
    Topology.isOpen_has_all_P
      (X := X)
      (A := interior (closure (interior A)))
      h_open