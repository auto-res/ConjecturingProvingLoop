

theorem Topology.P1_of_isClosed_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (h_open : IsOpen (A : Set X)) :
    Topology.P1 (X := X) A := by
  dsimp [Topology.P1]
  intro x hx
  -- Since `A` is open, its interior is itself.
  have h_int : interior (A : Set X) = A := by
    simpa using h_open.interior_eq
  -- Consequently, because `A` is closed, the closure of its interior is also `A`.
  have h_closure : closure (interior (A : Set X)) = A := by
    have : closure (interior (A : Set X)) = closure (A : Set X) := by
      simpa [h_int]
    simpa [h_closed.closure_eq] using this
  -- The desired membership follows by rewriting with `h_closure`.
  simpa [h_closure] using hx