

theorem closure_inter_eq_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    closure (A ∩ B : Set X) = A ∩ B := by
  have hClosed : IsClosed ((A ∩ B : Set X)) := hA.inter hB
  simpa using hClosed.closure_eq