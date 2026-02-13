

theorem interior_closure_has_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  have hAll := Topology.isOpen_has_all_Ps (X := X) (A := interior (closure A)) hOpen
  exact hAll.2.1