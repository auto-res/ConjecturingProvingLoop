

theorem isClosed_closure_interior_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (closure (interior (A : Set X)) ∩ closure (interior (B : Set X))) := by
  have hA : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  have hB : IsClosed (closure (interior (B : Set X))) := isClosed_closure
  exact hA.inter hB