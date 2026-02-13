

theorem closure_iInter_eq_iInter_of_closed
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X}
    (hS : ∀ i, IsClosed (S i)) :
    closure (⋂ i, S i : Set X) = ⋂ i, S i := by
  have hClosed : IsClosed (⋂ i, S i : Set X) :=
    isClosed_iInter (fun i ↦ hS i)
  simpa [hClosed.closure_eq]