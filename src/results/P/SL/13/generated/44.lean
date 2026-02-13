

theorem Topology.P1_interiorClosureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (interior (closure (interior (A : Set X)))) := by
  simpa using
    (Topology.P1_interior (X := X) (A := closure (interior A)))