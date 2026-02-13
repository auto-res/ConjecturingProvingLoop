

theorem Topology.closure_compl_eq_compl_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (Aᶜ) = (interior A)ᶜ := by
  classical
  ext x
  constructor
  · intro hx
    -- We show that `x ∉ interior A`.
    by_cases hxInt : x ∈ interior A
    · -- Derive a contradiction from `hx` and `hxInt`.
      have h_nonempty :=
        (mem_closure_iff).1 hx (interior A) isOpen_interior hxInt
      rcases h_nonempty with ⟨y, hy⟩
      have h_inA  : y ∈ A     := interior_subset hy.1
      have h_notA : y ∈ Aᶜ := hy.2
      have : False := h_notA h_inA
      exact (this.elim)
    · -- If `x ∉ interior A`, this is exactly the desired statement.
      exact hxInt
  · intro hx
    -- Here `hx` is `x ∉ interior A`; we prove `x ∈ closure (Aᶜ)`.
    have hNotInt : x ∉ interior A := hx
    -- Use the neighbourhood characterisation of the closure.
    have h_closure : x ∈ closure (Aᶜ) := by
      apply (mem_closure_iff).2
      intro U hUopen hxU
      -- We must show `(U ∩ Aᶜ).Nonempty`.
      by_contra h_empty
      -- `h_empty` says `U ⊆ A`.
      have h_sub : U ⊆ A := by
        intro y hyU
        by_contra hyNotA
        have h_inter : (U ∩ Aᶜ).Nonempty := ⟨y, ⟨hyU, hyNotA⟩⟩
        exact h_empty h_inter
      -- Hence `U ⊆ interior A` (since `U` is open and contained in `A`).
      have hU_interior : U ⊆ interior A :=
        interior_maximal h_sub hUopen
      -- This puts `x` in `interior A`, contradicting `hNotInt`.
      have : x ∈ interior A := hU_interior hxU
      exact (hNotInt this).elim
    exact h_closure