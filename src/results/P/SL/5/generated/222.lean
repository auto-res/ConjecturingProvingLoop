

theorem isClosed_closure_diff_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (A : Set X) \ interior (closure (A : Set X))) := by
  -- `closure A` is closed.
  have hClosedCl : IsClosed (closure (A : Set X)) := isClosed_closure
  -- The complement of an open set is closed; here the open set is `interior (closure A)`.
  have hClosedCompl : IsClosed ((interior (closure (A : Set X)))ᶜ) :=
    (isOpen_interior : IsOpen (interior (closure (A : Set X)))).isClosed_compl
  -- The desired set is the intersection of these two closed sets.
  simpa [Set.diff_eq] using hClosedCl.inter hClosedCompl