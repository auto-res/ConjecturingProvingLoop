

theorem Topology.interior_diff_eq_diff_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsOpen (A : Set X)) :
    interior (A \ B) = A \ closure B := by
  classical
  -- First inclusion: `interior (A \ B) ⊆ A \ closure B`.
  have h₁ : interior (A \ B) ⊆ A \ closure B := by
    intro x hxInt
    -- `x` lies in `A \ B`.
    have hxDiff : x ∈ A \ B := interior_subset hxInt
    have hxA    : x ∈ A := hxDiff.1
    -- Show `x ∉ closure B`.
    have hxNotCl : x ∉ closure B := by
      intro hxCl
      -- Any open neighbourhood of `x` meets `B`.
      have h_closure := (mem_closure_iff).1 hxCl
      -- The open set `interior (A \ B)` contains `x` and is disjoint from `B`,
      -- contradicting the previous statement.
      have h_nonempty : (interior (A \ B) ∩ B).Nonempty :=
        h_closure _ isOpen_interior hxInt
      rcases h_nonempty with ⟨y, ⟨hyInt, hyB⟩⟩
      have : y ∈ A \ B := interior_subset hyInt
      exact this.2 hyB
    exact ⟨hxA, hxNotCl⟩
  -- Second inclusion: `A \ closure B ⊆ interior (A \ B)`.
  have h₂ : A \ closure B ⊆ interior (A \ B) := by
    -- The set `A \ closure B` is open.
    have hOpenDiff : IsOpen (A \ closure B) := by
      have hOpenCompl : IsOpen ((closure B)ᶜ) :=
        (isClosed_closure : IsClosed (closure B)).isOpen_compl
      simpa [Set.diff_eq] using hA.inter hOpenCompl
    -- And it is contained in `A \ B`.
    have hSubset : (A \ closure B : Set X) ⊆ A \ B := by
      intro x hx
      have hxNotB : x ∉ B := by
        intro hxB
        have : x ∈ closure B := subset_closure hxB
        exact hx.2 this
      exact ⟨hx.1, hxNotB⟩
    -- Use maximality of the interior.
    exact interior_maximal hSubset hOpenDiff
  -- Combine the two inclusions to obtain equality.
  exact Set.Subset.antisymm h₁ h₂