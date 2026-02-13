

theorem Topology.closure_interior_eq_of_isClosed_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hA_open : IsOpen A) :
    closure (interior A) = A := by
  -- The interior of an open set is itself.
  have hInt : interior A = A := hA_open.interior_eq
  -- The closure of a closed set is itself.
  have hCl : closure A = A := hA_closed.closure_eq
  -- Combine the two equalities to obtain the result.
  simpa [hInt, hCl]