

theorem closure_union_five {X : Type*} [TopologicalSpace X]
    {A B C D E : Set X} :
    closure (A ∪ B ∪ C ∪ D ∪ E : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E := by
  -- Regroup the unions so that `closure_union` is applicable.
  have h₁ :
      closure (A ∪ B ∪ C ∪ D ∪ E : Set X) =
        closure ((A ∪ B ∪ C ∪ D) ∪ E : Set X) := by
    simpa [Set.union_assoc]
  -- Distribute `closure` over the last union.
  have h₂ :
      closure ((A ∪ B ∪ C ∪ D) ∪ E : Set X) =
        closure (A ∪ B ∪ C ∪ D : Set X) ∪ closure E := by
    simpa using
      closure_union (A := (A ∪ B ∪ C ∪ D : Set X)) (B := E)
  -- Use the existing four-set lemma.
  have h₃ :
      closure (A ∪ B ∪ C ∪ D : Set X) =
        closure A ∪ closure B ∪ closure C ∪ closure D := by
    simpa using
      closure_union_four (X := X)
        (A := A) (B := B) (C := C) (D := D)
  -- Combine the equalities and reassociate unions.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E : Set X)
        = closure ((A ∪ B ∪ C ∪ D) ∪ E : Set X) := by
          simpa [Set.union_assoc] using h₁
    _ = closure (A ∪ B ∪ C ∪ D : Set X) ∪ closure E := by
          simpa using h₂
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D) ∪ closure E := by
          simpa [h₃]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E := by
          simpa [Set.union_assoc]