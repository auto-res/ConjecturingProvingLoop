

theorem Topology.closureInteriorClosure_satisfies_P1
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure A))) := by
  have hP1 : Topology.P1 (interior (closure A)) :=
    Topology.isOpen_implies_P1 (X := X) (A := interior (closure A)) isOpen_interior
  simpa using
    Topology.closure_has_P1_of_P1 (X := X) (A := interior (closure A)) hP1