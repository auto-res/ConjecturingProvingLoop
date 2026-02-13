

theorem P3_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_P3 (A := interior (closure A)) hOpen