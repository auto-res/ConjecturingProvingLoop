

theorem closure_union_six {X : Type*} [TopologicalSpace X]
    {A B C D E F : Set X} :
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪ closure F := by
  -- Reassociate the unions so that `closure_union` can be applied.
  have h₁ :
      closure (A ∪ B ∪ C ∪ D ∪ E ∪ F : Set X) =
        closure ((A ∪ B ∪ C ∪ D ∪ E) ∪ F : Set X) := by
    simpa [Set.union_assoc]
  -- Distribute `closure` over the last union.
  have h₂ :
      closure ((A ∪ B ∪ C ∪ D ∪ E) ∪ F : Set X) =
        closure (A ∪ B ∪ C ∪ D ∪ E : Set X) ∪ closure F := by
    simpa using
      closure_union
        (A := (A ∪ B ∪ C ∪ D ∪ E : Set X))
        (B := F)
  -- Use the existing five-set lemma.
  have h₃ :
      closure (A ∪ B ∪ C ∪ D ∪ E : Set X) =
        closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E := by
    simpa using
      closure_union_five (X := X)
        (A := A) (B := B) (C := C) (D := D) (E := E)
  -- Assemble the pieces and tidy up with associativity of `∪`.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F : Set X)
        = closure ((A ∪ B ∪ C ∪ D ∪ E) ∪ F : Set X) := by
            simpa [Set.union_assoc] using h₁
    _ = closure (A ∪ B ∪ C ∪ D ∪ E : Set X) ∪ closure F := by
            simpa using h₂
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E) ∪ closure F := by
            simpa [h₃]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪ closure F := by
            simpa [Set.union_assoc]