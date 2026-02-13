

theorem Topology.interior_eq_of_P2_and_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) (hClosed : IsClosed A) :
    interior A = A := by
  -- First, deduce `P3 A` from the given `P2 A`.
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  -- Apply the existing result for `P3` sets that are closed.
  exact
    Topology.interior_eq_of_P3_and_isClosed (X := X) (A := A) hP3 hClosed