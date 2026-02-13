

theorem P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  exact Topology.P2_of_open hOpen