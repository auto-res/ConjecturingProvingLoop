

theorem Topology.closure_interior_eq_self_of_isClosed_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (h_open : IsOpen (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  -- Since `A` is open, its interior is itself.
  have h_int : interior (A : Set X) = A := h_open.interior_eq
  -- Since `A` is closed, its closure is itself.
  have h_closure : closure (A : Set X) = A := h_closed.closure_eq
  -- Rewrite and finish.
  calc
    closure (interior (A : Set X)) = closure (A : Set X) := by
      simpa [h_int]
    _ = A := h_closure