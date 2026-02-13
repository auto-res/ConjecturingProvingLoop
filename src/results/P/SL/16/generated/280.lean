

theorem Topology.open_and_closed_iff_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (IsOpen A ∧ IsClosed A) ↔ interior A = closure A := by
  constructor
  · rintro ⟨hOpen, hClosed⟩
    have hInt : interior A = A := hOpen.interior_eq
    have hCl : closure A = A := hClosed.closure_eq
    simpa [hInt, hCl]
  · intro h_eq
    exact
      Topology.open_and_closed_of_interior_eq_closure
        (X := X) (A := A) h_eq