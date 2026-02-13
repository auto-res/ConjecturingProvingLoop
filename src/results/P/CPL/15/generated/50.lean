

theorem interior_eq_self_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X} (h3 : P3 A) (hcl : IsClosed A) : interior A = A := by
  -- `A` is closed, so its closure is itself.
  have h_cl : closure (A : Set X) = A := hcl.closure_eq
  -- From `P3_closed_iff_eq_interior_closure` we obtain `interior (closure A) = A`.
  have h_int_closure : interior (closure A) = A :=
    (P3_closed_iff_eq_interior_closure (A := A) hcl).1 h3
  -- Rewriting `closure A` with `A` gives the desired result.
  simpa [h_cl] using h_int_closure