

theorem closure_iInter_eq_iInter_of_closed {ι : Sort _} {X : Type _}
    [TopologicalSpace X] (A : ι → Set X) (hClosed : ∀ i, IsClosed (A i)) :
    closure (⋂ i, A i : Set X) = ⋂ i, A i := by
  have h : IsClosed (⋂ i, A i : Set X) := isClosed_iInter (fun i ↦ hClosed i)
  simpa using h.closure_eq