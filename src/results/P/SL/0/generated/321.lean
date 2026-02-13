

theorem interior_inter_three_subset_interiors {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    interior ((A ∩ B ∩ C) : Set X) ⊆
      interior (A : Set X) ∩ interior (B : Set X) ∩ interior (C : Set X) := by
  intro x hx
  -- `A ∩ B ∩ C` is contained in each of `A`, `B`, and `C`.
  have hSubA : (A ∩ B ∩ C : Set X) ⊆ (A : Set X) := by
    intro y hy; exact hy.1.1
  have hSubB : (A ∩ B ∩ C : Set X) ⊆ (B : Set X) := by
    intro y hy; exact (hy.1).2
  have hSubC : (A ∩ B ∩ C : Set X) ⊆ (C : Set X) := by
    intro y hy; exact hy.2
  -- Apply monotonicity of `interior` to transfer the membership.
  have hxA : x ∈ interior (A : Set X) := (interior_mono hSubA) hx
  have hxB : x ∈ interior (B : Set X) := (interior_mono hSubB) hx
  have hxC : x ∈ interior (C : Set X) := (interior_mono hSubC) hx
  exact And.intro (And.intro hxA hxB) hxC