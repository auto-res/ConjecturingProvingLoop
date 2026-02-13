

theorem Topology.interior_closure_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (interior (closure A)) ∧
      Topology.P2 (X := X) (interior (closure A)) ∧
      Topology.P3 (X := X) (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact
    Topology.isOpen_satisfies_P1_P2_P3
      (X := X) (A := interior (closure A)) hOpen