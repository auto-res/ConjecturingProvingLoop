

theorem interior_eq_self_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_int : interior A = A) :
    Topology.P1 A := by
  -- The equality `interior A = A` shows that `A` is open.
  have hOpen : IsOpen A := by
    simpa [h_int] using (isOpen_interior : IsOpen (interior A))
  -- Openness of `A` implies `P1 A`.
  simpa using Topology.isOpen_imp_P1 (X := X) (A := A) hOpen