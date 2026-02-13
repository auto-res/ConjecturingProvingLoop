

theorem Topology.closureInterior_eq_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → closure (interior (closure A)) = closure A := by
  intro hP3
  simpa using
    (Topology.closureInteriorClosure_eq_closure_of_P3 (X := X) (A := A) hP3)