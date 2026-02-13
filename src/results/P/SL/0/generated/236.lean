

theorem P1_iff_P3_of_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (A : Set X))) ↔
      Topology.P3 (interior (closure (A : Set X))) := by
  have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  exact
    Topology.P1_iff_P3_of_isOpen
      (X := X) (A := interior (closure (A : Set X))) hOpen