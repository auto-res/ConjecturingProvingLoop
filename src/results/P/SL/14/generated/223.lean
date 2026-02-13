

theorem Topology.interior_diff_eq_closure_compl
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) :
    interior (A \ B : Set X) = A \ closure B := by
  classical
  -- First, show `interior (A \ B) ⊆ A \ closure B`.
  have h₁ : interior (A \ B : Set X) ⊆ A \ closure B := by
    intro x hx_int
    -- `x ∈ A \ B`
    have hx_mem : (x : X) ∈ A \ B :=
      (interior_subset : interior (A \ B : Set X) ⊆ A \ B) hx_int
    rcases hx_mem with ⟨hxA, hxNotB⟩
    -- Show `x ∉ closure B`
    have hNotClB : (x : X) ∉ closure B := by
      by_contra h_cl
      -- Every neighbourhood of `x` meets `B`, so in particular `interior (A \ B)` does.
      have h_nonempty :
          ((interior (A \ B) : Set X) ∩ B).Nonempty :=
        ((mem_closure_iff).1 h_cl) (interior (A \ B)) isOpen_interior hx_int
      rcases h_nonempty with ⟨y, hyInt, hyB⟩
      -- But `interior (A \ B)` is disjoint from `B`.
      have : (y : X) ∈ A \ B :=
        (interior_subset : interior (A \ B) ⊆ A \ B) hyInt
      exact this.2 hyB
    exact And.intro hxA hNotClB
  -- Second, show `A \ closure B ⊆ interior (A \ B)`.
  have h₂ : A \ closure B ⊆ interior (A \ B : Set X) := by
    intro x hx
    rcases hx with ⟨hxA, hxNotClB⟩
    -- The set `U = A ∩ (closure B)ᶜ` is an open neighbourhood of `x`
    -- contained in `A \ B`.
    let U : Set X := A ∩ (closure B)ᶜ
    have hU_open : IsOpen U :=
      IsOpen.inter hA isClosed_closure.isOpen_compl
    have hxU : (x : X) ∈ U := by
      have : (x : X) ∈ (closure B)ᶜ := hxNotClB
      simpa [U] using And.intro hxA this
    have hU_subset : (U : Set X) ⊆ A \ B := by
      intro y hy
      rcases hy with ⟨hyA, hyNotClB⟩
      have hyNotB : (y : X) ∉ B := by
        intro hyB
        have : (y : X) ∈ closure B := subset_closure hyB
        exact hyNotClB this
      exact And.intro hyA hyNotB
    -- Since `U` is open and contained in `A \ B`, it lies in the interior.
    have hU_interior : (U : Set X) ⊆ interior (A \ B : Set X) :=
      interior_maximal hU_subset hU_open
    exact hU_interior hxU
  -- Combine both inclusions to obtain equality.
  exact Set.Subset.antisymm h₁ h₂