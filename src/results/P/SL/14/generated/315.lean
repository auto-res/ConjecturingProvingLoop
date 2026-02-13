

theorem Topology.interior_diff_eq_self_of_open_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen (A : Set X)) (hB_closed : IsClosed (B : Set X)) :
    interior (A \ B : Set X) = A \ B := by
  have h :=
    Topology.interior_diff_eq_interior_diff_closed
      (X := X) (A := A) (B := B) hB_closed
  simpa [hA_open.interior_eq] using h