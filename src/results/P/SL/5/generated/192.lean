

theorem isClosed_closure_diff_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (A : Set X) \ interior A) := by
  have h₁ : IsClosed (closure (A : Set X)) := isClosed_closure
  have h₂ : IsClosed ((interior (A : Set X))ᶜ) := by
    simpa using (isOpen_interior : IsOpen (interior (A : Set X))).isClosed_compl
  simpa [Set.diff_eq, Set.inter_comm] using h₁.inter h₂