

theorem isClosed_closure_interior_diff_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    IsClosed (closure (interior (A : Set X)) \ interior (A : Set X)) := by
  -- Rewrite the set as an intersection of two closed sets.
  have h_eq :
      (closure (interior (A : Set X)) \ interior (A : Set X)) =
        closure (interior (A : Set X)) ∩ (interior (A : Set X))ᶜ := rfl
  -- `closure (interior A)` is closed.
  have h_closed₁ : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- The complement of `interior A` is closed because `interior A` is open.
  have h_closed₂ : IsClosed ((interior (A : Set X))ᶜ) :=
    (isOpen_interior : IsOpen (interior (A : Set X))).isClosed_compl
  -- The intersection of closed sets is closed.
  simpa [h_eq] using h_closed₁.inter h_closed₂