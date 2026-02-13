

theorem Topology.P2_of_isClopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClopen A → Topology.P2 A := by
  intro hClopen
  exact Topology.P2_of_isOpen (A := A) hClopen.2