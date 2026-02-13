

theorem Topology.closureInterior_satisfies_P1
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior A)) := by
  have h_int_P1 : Topology.P1 (interior A) :=
    Topology.interior_satisfies_P1 (X := X) A
  exact Topology.closure_has_P1_of_P1 (X := X) (A := interior A) h_int_P1