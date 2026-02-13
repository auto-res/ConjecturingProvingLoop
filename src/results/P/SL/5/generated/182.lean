

theorem IsOpen.diff {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsClosed (B : Set X)) :
    IsOpen (A \ B) := by
  simpa [Set.diff_eq] using hA.inter hB.isOpen_compl