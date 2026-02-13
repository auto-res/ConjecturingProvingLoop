

theorem Topology.frontier_isClosed {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (frontier A) := by
  -- `closure A` and `closure (Aᶜ)` are both closed, so their intersection is closed.
  have hClosed : IsClosed (closure A ∩ closure (Aᶜ)) :=
    (isClosed_closure : IsClosed (closure A)).inter
      (isClosed_closure : IsClosed (closure (Aᶜ)))
  -- Rewrite the intersection as the frontier.
  simpa [Topology.frontier_eq_closure_inter_closure_compl (A := A)] using hClosed