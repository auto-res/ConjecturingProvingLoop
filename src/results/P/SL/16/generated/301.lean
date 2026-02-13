

theorem Topology.P2_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (interior (closure A)) :=
  Topology.P2_interior_closure (X := X) (A := A)