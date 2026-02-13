

theorem Topology.P3_interior_inter {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 (interior (A ∩ B)) := by
  have hOpen : IsOpen (interior (A ∩ B)) := isOpen_interior
  exact Topology.P3_of_isOpen (A := interior (A ∩ B)) hOpen