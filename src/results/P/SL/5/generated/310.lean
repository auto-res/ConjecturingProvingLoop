

theorem closure_union_eleven {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I J K : Set X} :
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
        closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J ∪ closure K := by
  -- First, distribute `closure` over the last union using the two-set lemma.
  have h₁ :
      closure
        ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J) ∪ K : Set X) =
        closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J : Set X) ∪
          closure K := by
    simpa using
      closure_union
        (A :=
          (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J : Set X))
        (B := K)
  -- Apply the already-proved ten-set lemma to the first part.
  have h₂ :
      closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J : Set X) =
        closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
          closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J := by
    simpa using
      closure_union_ten (X := X)
        (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
        (G := G) (H := H) (I := I) (J := J)
  -- Assemble the equalities and tidy up with associativity of `∪`.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K : Set X)
        = closure
            ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J) ∪ K : Set X) := by
          simpa [Set.union_assoc]
    _ = closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J : Set X) ∪
          closure K := by
          simpa using h₁
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
          closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J) ∪
          closure K := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
        closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J ∪
        closure K := by
          simp [Set.union_assoc]