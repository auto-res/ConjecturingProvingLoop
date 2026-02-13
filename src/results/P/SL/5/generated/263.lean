

theorem isClosed_closure_interior_diff_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior (A : Set X)) \ interior (closure (A : Set X))) := by
  -- `closure (interior A)` is closed.
  have h₁ : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- The complement of the open set `interior (closure A)` is closed.
  have h₂ : IsClosed ((interior (closure (A : Set X)))ᶜ) :=
    (isOpen_interior : IsOpen (interior (closure (A : Set X)))).isClosed_compl
  -- The difference is the intersection of these two closed sets.
  simpa [Set.diff_eq, Set.inter_comm] using h₁.inter h₂