

theorem Topology.interior_closure_eq_self_of_clopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) (hA_open : IsOpen A) :
    interior (closure A) = A := by
  calc
    interior (closure A) = interior A := by
      simpa using
        (Topology.interior_closure_eq_interior_of_closed (A := A) hA_closed)
    _ = A := by
      simpa using hA_open.interior_eq