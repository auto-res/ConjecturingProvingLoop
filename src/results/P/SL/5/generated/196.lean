

theorem IsClosed.diff {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsOpen (B : Set X)) :
    IsClosed (A \ B) := by
  simpa [Set.diff_eq] using hA.inter hB.isClosed_compl