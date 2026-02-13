

theorem isClosed_closure_inter {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (closure A ∩ closure B) := by
  simpa using (isClosed_closure.inter isClosed_closure)