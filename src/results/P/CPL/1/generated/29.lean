

theorem P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P3 A) (hB : P3 B) (hC : P3 C) : P3 (A ∪ B ∪ C) := by
  -- Step 1: obtain `P3` for `A ∪ B`.
  have hAB : P3 (A ∪ B) :=
    P3_union (A := A) (B := B) hA hB
  -- Step 2: combine with `C`.
  have hABC : P3 ((A ∪ B) ∪ C) :=
    P3_union (A := (A ∪ B)) (B := C) hAB hC
  -- Reassociate unions to match the goal.
  simpa [Set.union_assoc] using hABC

theorem exists_compact_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ K, IsCompact K ∧ K ⊆ A ∧ P1 K := by
  refine ⟨(∅ : Set X), isCompact_empty, Set.empty_subset _, P1_empty⟩