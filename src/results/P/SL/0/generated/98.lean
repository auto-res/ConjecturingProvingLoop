

theorem interior_closure_inter_subset_interiors {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure ((A ∩ B) : Set X)) ⊆
      interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) := by
  -- First, relate `closure (A ∩ B)` to `closure A` and `closure B`.
  have hSubA :
      closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) := by
    have hAB_SubA : (A ∩ B : Set X) ⊆ (A : Set X) := by
      intro x hx
      exact hx.1
    exact closure_mono hAB_SubA
  have hSubB :
      closure ((A ∩ B) : Set X) ⊆ closure (B : Set X) := by
    have hAB_SubB : (A ∩ B : Set X) ⊆ (B : Set X) := by
      intro x hx
      exact hx.2
    exact closure_mono hAB_SubB
  -- Use monotonicity of `interior` to obtain the desired inclusions.
  have hIntSubA :
      interior (closure ((A ∩ B) : Set X)) ⊆
        interior (closure (A : Set X)) := interior_mono hSubA
  have hIntSubB :
      interior (closure ((A ∩ B) : Set X)) ⊆
        interior (closure (B : Set X)) := interior_mono hSubB
  -- Combine the two inclusions.
  intro x hx
  exact And.intro (hIntSubA hx) (hIntSubB hx)