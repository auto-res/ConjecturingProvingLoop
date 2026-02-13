

theorem P2_sUnionᵢ {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P2 (A i)) : P2 (⋃ i, A i) := by
  simpa using P2_unionᵢ (A := A) h

theorem P3_Union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : P3 A) (hB : P3 B) (hC : P3 C) (hD : P3 D) : P3 (A ∪ B ∪ C ∪ D) := by
  -- Step 1: obtain `P3` for `A ∪ B`
  have hAB : P3 (A ∪ B) :=
    P3_union (A := A) (B := B) hA hB
  -- Step 2: obtain `P3` for `A ∪ B ∪ C`
  have hABC : P3 (A ∪ B ∪ C) := by
    have : P3 ((A ∪ B) ∪ C) :=
      P3_union (A := (A ∪ B)) (B := C) hAB hC
    simpa [Set.union_assoc] using this
  -- Step 3: obtain `P3` for `A ∪ B ∪ C ∪ D`
  have hABCD : P3 (A ∪ B ∪ C ∪ D) := by
    have : P3 ((A ∪ B ∪ C) ∪ D) :=
      P3_union (A := (A ∪ B ∪ C)) (B := D) hABC hD
    simpa [Set.union_assoc] using this
  exact hABCD

theorem interior_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : interior A ⊆ interior (closure (interior A)) := by
  intro x hx
  exact h (interior_subset hx)