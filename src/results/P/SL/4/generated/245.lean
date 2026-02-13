

theorem frontier_isClosed {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (frontier A) := by
  -- Express `frontier A` as an intersection of two closed sets.
  have h_eq : (frontier A : Set X) = closure A ∩ closure (Aᶜ) := by
    simpa using
      (closure_inter_closure_compl_eq_frontier (X := X) (A := A)).symm
  -- The intersection of two closed sets is closed.
  have h_closed : IsClosed (closure A ∩ closure (Aᶜ)) := by
    have h₁ : IsClosed (closure A) := isClosed_closure
    have h₂ : IsClosed (closure (Aᶜ)) := isClosed_closure
    exact h₁.inter h₂
  simpa [h_eq] using h_closed