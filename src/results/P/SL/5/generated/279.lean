

theorem closure_union_nine {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I : Set X} :
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
        closure F ∪ closure G ∪ closure H ∪ closure I := by
  -- First, distribute `closure` over the last union.
  have h₁ :
      closure ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H) ∪ I : Set X) =
        closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H : Set X) ∪ closure I := by
    simpa using
      closure_union
        (A := (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H : Set X))
        (B := I)
  -- Next, apply the existing eight‐set lemma.
  have h₂ :
      closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H : Set X) =
        closure A ∪ closure B ∪ closure C ∪ closure D ∪
          closure E ∪ closure F ∪ closure G ∪ closure H := by
    simpa using
      closure_union_eight (X := X)
        (A := A) (B := B) (C := C) (D := D)
        (E := E) (F := F) (G := G) (H := H)
  -- Assemble the equalities and reassociate unions.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I : Set X) =
        closure ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H) ∪ I : Set X) := by
          simpa [Set.union_assoc]
    _ = closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H : Set X) ∪ closure I := by
          simpa using h₁
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D ∪
          closure E ∪ closure F ∪ closure G ∪ closure H) ∪ closure I := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
          closure F ∪ closure G ∪ closure H ∪ closure I := by
          simp [Set.union_assoc]