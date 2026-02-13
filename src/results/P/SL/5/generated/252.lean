

theorem closure_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} :
    closure (A ∪ B ∪ C ∪ D : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D := by
  -- First, distribute `closure` over `A ∪ B ∪ C`.
  have hABC :
      closure (A ∪ B ∪ C : Set X) =
        closure A ∪ closure B ∪ closure C :=
    closure_union_three (X := X) (A := A) (B := B) (C := C)
  -- Now regroup the unions and apply `closure_union` once more.
  calc
    closure (A ∪ B ∪ C ∪ D : Set X)
        = closure ((A ∪ B ∪ C) ∪ D : Set X) := by
            simpa [Set.union_assoc]
    _ = closure (A ∪ B ∪ C : Set X) ∪ closure D := by
            simpa using
              closure_union (A := (A ∪ B ∪ C : Set X)) (B := D)
    _ = (closure A ∪ closure B ∪ closure C) ∪ closure D := by
            simpa [hABC]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D := by
            simpa [Set.union_assoc]