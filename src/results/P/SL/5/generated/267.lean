

theorem closure_union_eight {X : Type*} [TopologicalSpace X]
    {A B C D E F G H : Set X} :
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪
      closure E ∪ closure F ∪ closure G ∪ closure H := by
  -- Distribute `closure` over the last union.
  have h₁ :
      closure ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) ∪ H : Set X) =
        closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G : Set X) ∪ closure H := by
    simpa using
      closure_union
        (A := (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G : Set X))
        (B := H)
  -- Apply the seven-set lemma.
  have h₂ :
      closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G : Set X) =
        closure A ∪ closure B ∪ closure C ∪ closure D ∪
        closure E ∪ closure F ∪ closure G := by
    simpa using
      closure_union_seven (X := X)
        (A := A) (B := B) (C := C) (D := D) (E := E) (F := F) (G := G)
  -- Assemble the equalities and reassociate unions.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H : Set X)
        = closure ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) ∪ H : Set X) := by
          simpa [Set.union_assoc]
    _ = closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G : Set X) ∪ closure H := by
          simpa using h₁
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D ∪
          closure E ∪ closure F ∪ closure G) ∪ closure H := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪
        closure E ∪ closure F ∪ closure G ∪ closure H := by
          simp [Set.union_assoc]