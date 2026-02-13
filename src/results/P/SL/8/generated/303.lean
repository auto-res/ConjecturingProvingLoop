

theorem closure_union_eq_of_isClosed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∪ B) = A ∪ B := by
  calc
    closure (A ∪ B) = closure A ∪ closure B := by
      simpa using
        (closure_union : closure (A ∪ B) = closure A ∪ closure B)
    _ = A ∪ B := by
      simpa [hA.closure_eq, hB.closure_eq]