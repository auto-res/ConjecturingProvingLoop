

theorem interior_inter_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ B := by
  -- First, show `interior (A ∩ B) ⊆ interior A ∩ B`.
  have h₁ : interior (A ∩ B) ⊆ interior A ∩ interior B :=
    interior_inter_subset (A := A) (B := B)
  have h₁' : interior (A ∩ B) ⊆ interior A ∩ B := by
    simpa [hB.interior_eq] using h₁
  -- Second, show `interior A ∩ B ⊆ interior (A ∩ B)`.
  have h₂ : interior A ∩ B ⊆ interior (A ∩ B) := by
    intro x hx
    rcases hx with ⟨hxIntA, hxB⟩
    -- `x` lies in the open set `interior A ∩ B`, which is contained in `A ∩ B`.
    have hOpen : IsOpen (interior A ∩ B) := isOpen_interior.inter hB
    have hSub : (interior A ∩ B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact ⟨(interior_subset : interior A ⊆ A) hy.1, hy.2⟩
    exact
      (interior_maximal hSub hOpen) ⟨hxIntA, hxB⟩
  exact Set.Subset.antisymm h₁' h₂