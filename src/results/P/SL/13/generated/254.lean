

theorem Topology.isClosed_boundary {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure (A : Set X) \ interior A) := by
  -- The closure of a set is closed.
  have h₁ : IsClosed (closure (A : Set X)) := isClosed_closure
  -- The complement of the interior is closed.
  have h₂ : IsClosed ((interior (A : Set X))ᶜ) := by
    have : IsOpen (interior (A : Set X)) := isOpen_interior
    exact this.isClosed_compl
  -- Express the set as an intersection of two closed sets.
  simpa [Set.diff_eq] using h₁.inter h₂