

theorem interior_eq_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P3 A → interior (A : Set X) = A := by
  intro hP3
  -- From `P3` and the fact that `A` is closed, deduce that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    ((Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1) hP3
  -- The interior of an open set coincides with the set itself.
  simpa [hOpen.interior_eq]