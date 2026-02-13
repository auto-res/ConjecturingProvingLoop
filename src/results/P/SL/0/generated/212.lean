

theorem interior_closure_union_three_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    (interior (closure (A : Set X)) ∪ interior (closure (B : Set X)) ∪
        interior (closure (C : Set X))) ⊆
      interior (closure (A ∪ B ∪ C : Set X)) := by
  intro x hx
  -- Split according to the part of the three‐way union that contains `x`.
  cases hx with
  | inl hAB =>
      -- `x` lies in the union of the first two interiors.
      have h₁ :
          interior (closure (A : Set X)) ∪ interior (closure (B : Set X)) ⊆
            interior (closure (A ∪ B : Set X)) :=
        interior_closure_union_subset (X := X) (A := A) (B := B)
      have hxAB : x ∈ interior (closure (A ∪ B : Set X)) := h₁ hAB
      -- Enlarge `A ∪ B` to `A ∪ B ∪ C`.
      have hMono :
          interior (closure (A ∪ B : Set X)) ⊆
            interior (closure (A ∪ B ∪ C : Set X)) := by
        have hCl :
            closure (A ∪ B : Set X) ⊆ closure (A ∪ B ∪ C : Set X) := by
          have hSub : (A ∪ B : Set X) ⊆ A ∪ B ∪ C := by
            intro y hy
            cases hy with
            | inl hyA => exact Or.inl (Or.inl hyA)
            | inr hyB => exact Or.inl (Or.inr hyB)
          exact closure_mono hSub
        exact interior_mono hCl
      exact hMono hxAB
  | inr hC =>
      -- `x` lies in the third interior.
      have hCl :
          closure (C : Set X) ⊆ closure (A ∪ B ∪ C : Set X) := by
        have hSub : (C : Set X) ⊆ A ∪ B ∪ C := by
          intro y hy
          exact Or.inr hy
        exact closure_mono hSub
      have hMono :
          interior (closure (C : Set X)) ⊆
            interior (closure (A ∪ B ∪ C : Set X)) :=
        interior_mono hCl
      exact hMono hC