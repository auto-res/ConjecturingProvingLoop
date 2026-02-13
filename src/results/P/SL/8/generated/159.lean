

theorem interior_eq_self_imp_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_int : interior A = A) :
    Topology.P2 A := by
  -- From `interior A = A`, we deduce that `A` is open.
  have hOpen : IsOpen A := by
    simpa [h_int] using (isOpen_interior : IsOpen (interior A))
  -- Openness immediately yields `P2`.
  exact Topology.isOpen_imp_P2 (X := X) (A := A) hOpen