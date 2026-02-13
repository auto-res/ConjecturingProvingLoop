

theorem isOpen_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X))
    (hC : IsOpen (C : Set X)) (hD : IsOpen (D : Set X)) :
    IsOpen ((A ∪ B ∪ C ∪ D) : Set X) := by
  -- First, the union `A ∪ B ∪ C` is open.
  have hABC : IsOpen ((A ∪ B ∪ C) : Set X) := by
    have hAB : IsOpen ((A ∪ B) : Set X) := hA.union hB
    simpa [Set.union_assoc] using hAB.union hC
  -- Adding `D` preserves openness.
  simpa [Set.union_assoc] using hABC.union hD