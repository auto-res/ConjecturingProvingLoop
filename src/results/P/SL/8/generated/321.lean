

theorem interior_compl_eq_compl_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (Aᶜ) = (closure A)ᶜ := by
  classical
  ext x
  constructor
  · -- `x ∈ interior (Aᶜ) → x ∉ closure A`
    intro hx
    -- Assume, for contradiction, that `x ∈ closure A`
    have h : x ∉ closure A := by
      intro hxCl
      -- Obtain an open neighbourhood `U` of `x` contained in `Aᶜ`
      rcases (Set.mem_interior).1 hx with ⟨U, hU_open, hU_sub, hxU⟩
      -- Since `x ∈ closure A`, `U` meets `A`
      have hNon : (U ∩ A).Nonempty :=
        (mem_closure_iff).1 hxCl U hU_open hxU
      rcases hNon with ⟨y, hyU, hyA⟩
      -- But `U ⊆ Aᶜ`, contradiction
      have : y ∈ Aᶜ := hU_sub hyU
      exact this hyA
    exact h
  · -- `x ∉ closure A → x ∈ interior (Aᶜ)`
    intro hx
    -- The set `V = (closure A)ᶜ` is open and contains `x`
    have hV_open : IsOpen ((closure A)ᶜ) := (isOpen_compl_iff).2 isClosed_closure
    have hxV : x ∈ (closure A)ᶜ := hx
    -- Show `V ⊆ Aᶜ`
    have hV_sub : (closure A)ᶜ ⊆ Aᶜ := by
      intro y hy
      by_cases hA : y ∈ A
      · have : (y : X) ∈ closure A := subset_closure hA
        exact (hy this).elim
      · exact hA
    -- Conclude that `x` lies in the interior of `Aᶜ`
    exact
      (Set.mem_interior).2 ⟨(closure A)ᶜ, hV_open, hV_sub, hxV⟩