

theorem interior_inter_left_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) :
    interior ((A ∩ B) : Set X) = (A : Set X) ∩ interior (B : Set X) := by
  -- First, show the left‐to‐right inclusion.
  have h₁ :
      (interior ((A ∩ B) : Set X) : Set X) ⊆
        (A : Set X) ∩ interior (B : Set X) := by
    intro x hx
    -- Membership in `interior (A ∩ B)` yields membership in `A ∩ B`.
    have hxAB : x ∈ (A : Set X) ∩ B := interior_subset hx
    -- Monotonicity: `interior (A ∩ B) ⊆ interior B`.
    have hxIntB : x ∈ interior (B : Set X) := by
      have hSub : ((A ∩ B) : Set X) ⊆ (B : Set X) := by
        intro y hy; exact hy.2
      exact (interior_mono hSub) hx
    exact And.intro hxAB.1 hxIntB
  -- Next, show the right‐to‐left inclusion.
  have h₂ :
      ((A : Set X) ∩ interior (B : Set X) : Set X) ⊆
        interior ((A ∩ B) : Set X) := by
    -- The set on the left is open, being the intersection of two open sets.
    have hOpen :
        IsOpen (((A : Set X) ∩ interior (B : Set X)) : Set X) :=
      hA.inter isOpen_interior
    -- It is contained in `A ∩ B`.
    have hSub :
        ((A : Set X) ∩ interior (B : Set X) : Set X) ⊆ (A : Set X) ∩ B := by
      intro y hy; exact And.intro hy.1 (interior_subset hy.2)
    -- Apply the maximality property of the interior.
    exact interior_maximal hSub hOpen
  exact Set.Subset.antisymm h₁ h₂