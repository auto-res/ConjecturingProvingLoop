

theorem P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P3 A) (hB : P3 B) (hC : P3 C) : P3 (A ∪ B ∪ C) := by
  have hAB : P3 (A ∪ B) := P3_union hA hB
  have hABC : P3 ((A ∪ B) ∪ C) := P3_union hAB hC
  simpa [Set.union_assoc] using hABC

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P2 A) (hB : P2 B) (hC : P2 C) : P2 (A ∪ B ∪ C) := by
  have hAB : P2 (A ∪ B) := P2_union (A := A) (B := B) hA hB
  have hABC : P2 ((A ∪ B) ∪ C) := P2_union hAB hC
  simpa [Set.union_assoc] using hABC

theorem P1_iff_P2_for_open_sets {X : Type*} [TopologicalSpace X] {A : Set X} (hop : IsOpen A) : P1 A ↔ P2 A := by
  constructor
  · intro _hP1
    exact P2_open (A := A) hop
  · intro hP2
    exact P1_of_P2 (A := A) hP2