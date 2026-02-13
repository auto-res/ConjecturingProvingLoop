

theorem Topology.P3_of_isClopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClopen A → Topology.P3 A := by
  intro hClopen
  exact Topology.P3_of_isOpen (A := A) hClopen.2