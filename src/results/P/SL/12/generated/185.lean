

theorem Topology.interior_closure_eq_closure_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure (A : Set X))) :
    interior (closure (A : Set X)) = closure A := by
  -- `closure A` is always closed.
  have h_closed : IsClosed (closure (A : Set X)) := isClosed_closure
  -- Apply the existing lemma for sets that are both closed and open.
  simpa [closure_closure] using
    Topology.interior_closure_eq_self_of_isClosed_isOpen
      (X := X) (A := closure A) h_closed h_open