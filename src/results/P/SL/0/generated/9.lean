

theorem interior_closure_has_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure A)) ∧ Topology.P3 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  have hAll := Topology.isOpen_has_all_Ps (X := X) (A := interior (closure A)) hOpen
  exact And.intro hAll.1 hAll.2.2