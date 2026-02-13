

theorem Topology.closed_P2_interiorClosureInterior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP2 : Topology.P2 (X := X) A) :
    interior (closure (interior A)) = A := by
  -- From closedness and `P2`, we already know two equalities.
  have h_cl : closure (interior A) = A :=
    Topology.closed_P2_closure_interior_eq_self (X := X) (A := A) hClosed hP2
  have h_int : interior A = A :=
    Topology.closed_P2_interior_eq_self (X := X) (A := A) hClosed hP2
  -- Rewrite twice to obtain the desired result.
  calc
    interior (closure (interior A)) = interior A := by
      simpa [h_cl]
    _ = A := by
      simpa [h_int]