

theorem Topology.isClosed_boundary {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure A \ interior A) := by
  have h₁ : IsClosed (closure A) := isClosed_closure
  have h₂ : IsClosed ((interior A)ᶜ) := (isOpen_interior : IsOpen (interior A)).isClosed_compl
  simpa [Set.diff_eq] using h₁.inter h₂