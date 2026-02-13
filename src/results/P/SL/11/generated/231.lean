

theorem closure_inter_eq_self_of_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∩ B) = A ∩ B := by
  have hClosed : IsClosed (A ∩ B) := hA.inter hB
  simpa using hClosed.closure_eq