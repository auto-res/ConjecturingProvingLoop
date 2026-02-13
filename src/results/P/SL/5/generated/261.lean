

theorem closure_union_seven {X : Type*} [TopologicalSpace X]
    {A B C D E F G : Set X} :
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪ closure F ∪ closure G := by
  have h₁ :
      closure ((A ∪ B ∪ C ∪ D ∪ E ∪ F) ∪ G : Set X) =
        closure (A ∪ B ∪ C ∪ D ∪ E ∪ F : Set X) ∪ closure G := by
    simpa using
      closure_union
        (A := (A ∪ B ∪ C ∪ D ∪ E ∪ F : Set X))
        (B := G)
  have h₂ :
      closure (A ∪ B ∪ C ∪ D ∪ E ∪ F : Set X) =
        closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪ closure F := by
    simpa using
      closure_union_six (X := X)
        (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G : Set X)
        = closure ((A ∪ B ∪ C ∪ D ∪ E ∪ F) ∪ G : Set X) := by
          simpa [Set.union_assoc]
    _ = closure (A ∪ B ∪ C ∪ D ∪ E ∪ F : Set X) ∪ closure G := by
          simpa using h₁
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪ closure F) ∪
          closure G := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪ closure F ∪
          closure G := by
          simp [Set.union_assoc]