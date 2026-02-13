

theorem interior_inter_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen (B : Set X)) :
    interior ((A ∩ B) : Set X) = interior (A : Set X) ∩ B := by
  -- Left-to-right inclusion.
  have h₁ :
      (interior ((A ∩ B) : Set X) : Set X) ⊆ interior (A : Set X) ∩ B := by
    intro x hx
    -- Membership in `interior (A ∩ B)` implies membership in `A ∩ B`.
    have hxAB : x ∈ (A : Set X) ∩ B := interior_subset hx
    -- Monotonicity of `interior` for the inclusion `A ∩ B ⊆ A`.
    have hxIntA : x ∈ interior (A : Set X) := by
      have hSub : (A ∩ B : Set X) ⊆ (A : Set X) := by
        intro y hy; exact hy.1
      exact (interior_mono hSub) hx
    exact And.intro hxIntA hxAB.2
  -- Right-to-left inclusion.
  have h₂ :
      (interior (A : Set X) ∩ B : Set X) ⊆ interior ((A ∩ B) : Set X) := by
    -- The set on the left is open as the intersection of two open sets.
    have hOpen : IsOpen ((interior (A : Set X)) ∩ B : Set X) :=
      (isOpen_interior).inter hB
    -- It is contained in `A ∩ B`.
    have hSub :
        ((interior (A : Set X)) ∩ B : Set X) ⊆ (A : Set X) ∩ B := by
      intro y hy; exact And.intro (interior_subset hy.1) hy.2
    -- Use the maximality property of `interior`.
    exact interior_maximal hSub hOpen
  exact Set.Subset.antisymm h₁ h₂