

theorem closure_inter_closure_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure (A : Set X) ∩ closure B) = closure A ∩ closure B := by
  have hClosed :
      IsClosed (closure (A : Set X) ∩ closure B) :=
    (isClosed_closure.inter isClosed_closure)
  simpa using hClosed.closure_eq