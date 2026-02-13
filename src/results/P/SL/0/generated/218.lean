

theorem closure_inter_eq_self_of_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    closure ((A ∩ B) : Set X) = (A ∩ B : Set X) := by
  simpa using (hA.inter hB).closure_eq