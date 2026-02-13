

theorem Topology.closed_P1_interior_closure_interior_eq_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP1 : Topology.P1 (X := X) A) :
    interior (closure (interior A)) = interior A := by
  -- First, use the general lemma that relates `P1` to interiors of closures.
  have h_eq :=
    Topology.interior_closure_interior_eq_interior_closure_of_P1
      (X := X) (A := A) hP1
  -- Since `A` is closed, its closure is itself. Substitute to conclude.
  simpa [hClosed.closure_eq] using h_eq