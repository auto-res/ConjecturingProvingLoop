

theorem closure_union_ten {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I J : Set X} :
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
        closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J := by
  -- Distribute `closure` over the last union using the two‐set lemma.
  have h₁ :
      closure ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) ∪ J : Set X) =
        closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I : Set X) ∪ closure J := by
    simpa using
      closure_union
        (A := (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I : Set X))
        (B := J)
  -- Apply the nine‐set lemma to the first part.
  have h₂ :
      closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I : Set X) =
        closure A ∪ closure B ∪ closure C ∪ closure D ∪
          closure E ∪ closure F ∪ closure G ∪ closure H ∪ closure I := by
    simpa using
      closure_union_nine (X := X)
        (A := A) (B := B) (C := C) (D := D) (E := E)
        (F := F) (G := G) (H := H) (I := I)
  -- Assemble the equalities and reassociate unions.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J : Set X)
        = closure ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) ∪ J : Set X) := by
          simpa [Set.union_assoc]
    _ = closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I : Set X) ∪ closure J := by
          simpa using h₁
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D ∪
          closure E ∪ closure F ∪ closure G ∪ closure H ∪ closure I) ∪
          closure J := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
          closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J := by
          simp [Set.union_assoc]