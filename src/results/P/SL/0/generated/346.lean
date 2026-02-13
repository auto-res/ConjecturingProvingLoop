

theorem closure_interior_eq_self_of_isClosed_and_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P1 A → closure (interior (A : Set X)) = A := by
  intro hP1
  -- `P1` gives `closure A = closure (interior A)`.
  have hEq :=
    (Topology.P1_iff_closure_eq_closure_interior
        (X := X) (A := A)).1 hP1
  -- Since `A` is closed, `closure A = A`.
  have hCl : closure (A : Set X) = A := hClosed.closure_eq
  -- Combine the two equalities.
  have h : (A : Set X) = closure (interior (A : Set X)) := by
    simpa [hCl] using hEq
  simpa using h.symm