

theorem interior_diff_eq_self_diff_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) :
    interior (A \ B) = A \ closure B := by
  classical
  -- First inclusion: `interior (A \ B) ⊆ A \ closure B`.
  have h₁ : interior (A \ B) ⊆ A \ closure B := by
    -- We already have a more precise inclusion into `interior A \ closure B`;
    -- for an open set `A`, `interior A = A`.
    have h := interior_diff_subset (X := X) (A := A) (B := B)
    simpa [hA.interior_eq] using h
  -- Second inclusion: `A \ closure B ⊆ interior (A \ B)`.
  have h₂ : A \ closure B ⊆ interior (A \ B) := by
    -- The set `A \ closure B` is open.
    have hOpenDiff : IsOpen (A \ closure B) := by
      -- `closure B` is closed, hence its complement is open.
      have hOpenCompl : IsOpen ((closure B)ᶜ) := by
        have hClosed : IsClosed (closure B) := isClosed_closure
        simpa using (isOpen_compl_iff).2 hClosed
      -- `A \ closure B` is the intersection of two open sets.
      simpa [Set.diff_eq] using hA.inter hOpenCompl
    -- Moreover, `A \ closure B ⊆ A \ B` because `B ⊆ closure B`.
    have hSubset : A \ closure B ⊆ A \ B := by
      intro x hx
      rcases hx with ⟨hxA, hxNotCl⟩
      have hxNotB : x ∉ B := by
        intro hxB
        have : (x : X) ∈ closure B := subset_closure hxB
        exact hxNotCl this
      exact And.intro hxA hxNotB
    -- Use the maximality property of the interior.
    exact interior_maximal hSubset hOpenDiff
  -- Combine the two inclusions for equality.
  exact Set.Subset.antisymm h₁ h₂