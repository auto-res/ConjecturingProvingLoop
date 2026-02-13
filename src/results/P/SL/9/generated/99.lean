

theorem Topology.closureInteriorClosure_eq_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    closure (interior (closure A)) = closure A := by
  have hP1 : Topology.P1 (A := A) :=
    Topology.P1_of_isOpen (A := A) hA
  simpa using
    (Topology.closureInterior_closure_eq_closure_of_P1 (A := A) hP1)