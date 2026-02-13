

theorem P123_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ∧ Topology.P2 (interior A) ∧ Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using Topology.P123_of_open hOpen