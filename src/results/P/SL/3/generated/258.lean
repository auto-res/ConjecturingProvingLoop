

theorem isClosed_closure_union_closure {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    IsClosed (closure (A : Set X) ∪ closure (B : Set X)) := by
  exact
    (isClosed_closure : IsClosed (closure (A : Set X))).union
      (isClosed_closure : IsClosed (closure (B : Set X)))