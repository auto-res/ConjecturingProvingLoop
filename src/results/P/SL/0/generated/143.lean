

theorem interior_eq_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P2 A → interior (A : Set X) = A := by
  intro hP2
  have hOpen : IsOpen (A : Set X) :=
    ((Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1) hP2
  simpa [hOpen.interior_eq] using rfl