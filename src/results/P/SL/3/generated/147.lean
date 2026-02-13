

theorem isClosed_closure_diff_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (A : Set X) \ interior (A : Set X)) := by
  -- Express the set as an intersection of two closed sets
  have h_eq :
      (closure (A : Set X) \ interior (A : Set X)) =
        closure (A : Set X) ∩ (interior (A : Set X))ᶜ := by
    rfl
  -- `closure A` is closed
  have h_closure : IsClosed (closure (A : Set X)) := isClosed_closure
  -- The complement of `interior A` is closed because `interior A` is open
  have h_compl : IsClosed ((interior (A : Set X))ᶜ) :=
    (isOpen_interior : IsOpen (interior (A : Set X))).isClosed_compl
  -- The intersection of two closed sets is closed
  simpa [h_eq] using h_closure.inter h_compl