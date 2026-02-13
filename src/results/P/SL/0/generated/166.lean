

theorem interior_inter_subset_interiors {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior ((A ∩ B) : Set X) ⊆ interior (A : Set X) ∩ interior (B : Set X) := by
  intro x hx
  -- `A ∩ B` is contained in `A`, hence so is its interior.
  have hA : (A ∩ B : Set X) ⊆ (A : Set X) := by
    intro y hy
    exact hy.1
  -- Symmetrically, `A ∩ B` is contained in `B`.
  have hB : (A ∩ B : Set X) ⊆ (B : Set X) := by
    intro y hy
    exact hy.2
  -- Apply monotonicity of `interior` to transfer the membership.
  have hxA : x ∈ interior (A : Set X) := (interior_mono hA) hx
  have hxB : x ∈ interior (B : Set X) := (interior_mono hB) hx
  exact And.intro hxA hxB