

theorem dense_compl_iff_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense ((Aᶜ) : Set X) ↔ interior (A : Set X) = ∅ := by
  classical
  -- `→`  Direction: density of the complement forces `interior A = ∅`.
  have h₁ : Dense (Aᶜ : Set X) → interior (A : Set X) = ∅ := by
    intro hDense
    by_contra hIntNe
    -- From `hIntNe`, obtain a point in `interior A`.
    have hIntNonempty : (interior (A : Set X)).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hIntNe
    -- Use the open–intersection characterization of density.
    have hProp :=
      (Topology.dense_iff_open_inter_nonempty
          (A := (Aᶜ : Set X))).1 hDense
    have hInter :=
      hProp (interior (A : Set X)) isOpen_interior hIntNonempty
    rcases hInter with ⟨x, ⟨hxCompl, hxInt⟩⟩
    -- But `interior A ⊆ A`, contradicting `x ∈ Aᶜ`.
    have hxA : (x : X) ∈ A := interior_subset hxInt
    exact (hxCompl hxA).elim
  -- `←`  Direction: empty interior implies density of the complement.
  have h₂ : interior (A : Set X) = ∅ → Dense (Aᶜ : Set X) := by
    intro hIntEmpty
    -- Establish the open–intersection property required for density.
    have hProp :
        ∀ U : Set X, IsOpen U → U.Nonempty →
          ((Aᶜ : Set X) ∩ U).Nonempty := by
      intro U hU_open hU_nonempty
      by_contra hEmpty
      -- If the intersection is empty, `U` is contained in `A`.
      have hSub : (U : Set X) ⊆ A := by
        intro x hxU
        by_contra hxNotA
        have hxCompl : x ∈ (Aᶜ : Set X) := hxNotA
        have hNE : ((Aᶜ : Set X) ∩ U).Nonempty := ⟨x, ⟨hxCompl, hxU⟩⟩
        exact hEmpty hNE
      -- Since `U` is open and `U ⊆ A`, we get `U ⊆ interior A = ∅`.
      have hSubInt : (U : Set X) ⊆ interior A :=
        interior_maximal hSub hU_open
      rcases hU_nonempty with ⟨x, hxU⟩
      have : (x : X) ∈ interior A := hSubInt hxU
      simpa [hIntEmpty] using this
    -- Apply the characterization to conclude density.
    exact
      (Topology.dense_iff_open_inter_nonempty (A := (Aᶜ : Set X))).2 hProp
  exact ⟨h₁, h₂⟩