

theorem Topology.isClosed_closure_diff_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure A \ interior A) := by
  have h₁ : IsClosed (closure A) := isClosed_closure
  have h₂ : IsClosed ((interior A)ᶜ) :=
    (isOpen_interior : IsOpen (interior A)).isClosed_compl
  -- `A \ B` is definitionally `A ∩ Bᶜ`, so this is an intersection of two closed sets.
  simpa [Set.diff_eq] using h₁.inter h₂