

theorem closure_inter_eq_inter_closure_of_isClosed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X)) :
    closure ((A ∩ B) : Set X) = closure (A : Set X) ∩ closure (B : Set X) := by
  simpa [hA_closed.closure_eq, hB_closed.closure_eq,
        (hA_closed.inter hB_closed).closure_eq]