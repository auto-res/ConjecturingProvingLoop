

theorem closure_interior_closure_eq_closure_of_P2_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) (closure (A : Set X))) :
    closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  -- `closure A` is always a closed set.
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  -- Apply the existing lemma for closed sets satisfying `P2`.
  simpa using
    Topology.closure_interior_eq_self_of_closed_and_P2
      (X := X) (A := closure (A : Set X)) hClosed h