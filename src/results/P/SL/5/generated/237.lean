

theorem closure_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure (A ∪ B ∪ C : Set X) = closure A ∪ closure B ∪ closure C := by
  -- First, group the union so that `closure_union` can be applied.
  have h₁ :
      closure ((A ∪ B) ∪ C : Set X) =
        closure (A ∪ B : Set X) ∪ closure C := by
    simpa using closure_union (A ∪ B : Set X) C
  -- Next, distribute `closure` over `A ∪ B`.
  have h₂ : closure (A ∪ B : Set X) = closure A ∪ closure B := by
    simpa using closure_union (A : Set X) B
  -- Assemble the pieces and tidy up with associativity of `∪`.
  calc
    closure (A ∪ B ∪ C : Set X)
        = closure ((A ∪ B) ∪ C : Set X) := by
            simpa [Set.union_assoc]
    _ = closure (A ∪ B : Set X) ∪ closure C := by
            simpa using h₁
    _ = (closure A ∪ closure B) ∪ closure C := by
            simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C := by
            simpa [Set.union_assoc]