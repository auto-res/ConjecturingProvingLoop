

theorem closure_inter_eq_self_of_isClosed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    closure ((A ∩ B) : Set X) = (A : Set X) ∩ B := by
  simpa using (hA.inter hB).closure_eq