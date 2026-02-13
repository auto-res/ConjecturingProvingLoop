

theorem P123_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure A)) ∧
    Topology.P2 (interior (closure A)) ∧
    Topology.P3 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  simpa using Topology.P123_of_open hOpen