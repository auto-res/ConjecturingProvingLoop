

theorem interior_closure_eq_self_of_closed_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 A) :
    interior (closure (A : Set X)) = A := by
  have hOpen : IsOpen (A : Set X) :=
    (Topology.P3_closed_iff_open (A := A) hClosed).1 hP3
  have hInt : interior (A : Set X) = A := hOpen.interior_eq
  have hClos : closure (A : Set X) = A := hClosed.closure_eq
  calc
    interior (closure (A : Set X)) = interior (A : Set X) := by
      simpa [hClos]
    _ = A := hInt