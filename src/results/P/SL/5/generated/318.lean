

theorem closure_union_twelve {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I J K L : Set X} :
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K ∪ L : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
        closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J ∪
        closure K ∪ closure L := by
  -- First, distribute `closure` over the final union with `L`.
  have h₁ :
      closure
          ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K) ∪ L : Set X) =
        closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K : Set X) ∪
          closure L := by
    simpa using
      closure_union
        (A :=
          (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K : Set X))
        (B := L)
  -- Next, apply the existing eleven‐set lemma to the first term.
  have h₂ :
      closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K : Set X) =
        closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
          closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J ∪
          closure K := by
    simpa using
      closure_union_eleven (X := X)
        (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
        (G := G) (H := H) (I := I) (J := J) (K := K)
  -- Combine the equalities and tidy up with associativity of `∪`.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K ∪ L : Set X)
        = closure
            ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K) ∪ L : Set X) := by
          simpa [Set.union_assoc]
    _ = closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K : Set X) ∪
          closure L := by
          simpa using h₁
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
          closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J ∪
          closure K) ∪ closure L := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
        closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J ∪
        closure K ∪ closure L := by
          simp [Set.union_assoc]