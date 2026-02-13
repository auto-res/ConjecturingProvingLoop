

theorem Topology.closureInterior_eq_of_isClosed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    closure (interior A) = (A : Set X) := by
  have hEq : closure (interior A) = closure (A : Set X) :=
    Topology.closureInterior_eq_closure_of_P2 (X := X) (A := A) hP2
  simpa [hA_closed.closure_eq] using hEq