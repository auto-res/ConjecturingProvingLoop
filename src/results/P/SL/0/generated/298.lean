

theorem isOpen_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) (hC : IsOpen (C : Set X)) :
    IsOpen ((A ∪ B ∪ C) : Set X) := by
  have hAB : IsOpen ((A ∪ B) : Set X) := hA.union hB
  simpa [Set.union_assoc] using hAB.union hC