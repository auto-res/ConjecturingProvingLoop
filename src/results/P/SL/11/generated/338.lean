

theorem interior_nonempty_iff_nonempty_of_closed_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP3 : Topology.P3 A) :
    (interior A).Nonempty ↔ A.Nonempty := by
  have hEq : interior A = A :=
    interior_eq_self_of_closed_of_P3 (A := A) hClosed hP3
  simpa [hEq]