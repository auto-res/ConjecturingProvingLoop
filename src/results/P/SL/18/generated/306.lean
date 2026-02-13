

theorem interior_diff_eq_self_of_open_closed
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU_open : IsOpen (U : Set X)) (hV_closed : IsClosed (V : Set X)) :
    interior (U \ V : Set X) = U \ V := by
  have h :=
    interior_diff_eq_diff_closure_of_open
      (X := X) (U := U) (V := V) hU_open
  simpa [hV_closed.closure_eq] using h