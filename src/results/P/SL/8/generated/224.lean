

theorem interior_eq_self_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_int : interior A = A) :
    Topology.P3 A := by
  have hOpen : IsOpen A := by
    simpa [h_int] using (isOpen_interior : IsOpen (interior A))
  simpa using Topology.isOpen_imp_P3 (X := X) (A := A) hOpen