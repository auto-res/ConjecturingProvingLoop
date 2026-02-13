

theorem Topology.interior_closure_eq_of_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClopen A) :
    interior (closure A) = (A : Set X) := by
  exact
    Topology.interior_closure_eq_of_isClosed_of_isOpen
      (A := A) hA.1 hA.2