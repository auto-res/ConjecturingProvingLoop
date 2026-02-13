

theorem isClosed_closure_inter_closure {X : Type*} [TopologicalSpace X] (A B : Set X) :
    IsClosed (closure (A : Set X) ∩ closure (B : Set X)) := by
  exact
    (isClosed_closure : IsClosed (closure (A : Set X))).inter
      (isClosed_closure : IsClosed (closure (B : Set X)))