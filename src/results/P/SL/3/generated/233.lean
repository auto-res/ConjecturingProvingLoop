

theorem isClosed_closure_diff_self_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    IsClosed (closure (A : Set X) \ A) := by
  -- Rewrite the set as an intersection of two closed sets.
  have h_eq : (closure (A : Set X) \ A) = closure (A : Set X) ∩ (Aᶜ : Set X) := rfl
  -- Both `closure A` and `Aᶜ` are closed.
  have h_closed₁ : IsClosed (closure (A : Set X)) := isClosed_closure
  have h_closed₂ : IsClosed ((Aᶜ) : Set X) := hA.isClosed_compl
  -- The intersection of closed sets is closed.
  simpa [h_eq] using h_closed₁.inter h_closed₂