

theorem Topology.P1_of_isClopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClopen A → Topology.P1 A := by
  intro hClopen
  exact Topology.P1_of_isOpen (A := A) hClopen.2