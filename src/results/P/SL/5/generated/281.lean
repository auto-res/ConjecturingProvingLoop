

theorem closure_interior_inter_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ∩ interior ((A : Set X)ᶜ) = (∅ : Set X) := by
  classical
  -- We show that the intersection contains no points.
  apply Set.eq_empty_iff_forall_not_mem.2
  intro x hx
  rcases hx with ⟨hxCl, hxIntCompl⟩
  -- Choose an open neighbourhood `U` of `x` contained in `Aᶜ`.
  rcases mem_interior.1 hxIntCompl with ⟨U, hUsub, hUopen, hxU⟩
  -- Because `x ∈ closure (interior A)`, the neighbourhood `U` meets `interior A`.
  have hNon : ((U : Set X) ∩ interior (A : Set X)).Nonempty := by
    have hClosure := (mem_closure_iff).1 hxCl
    -- Rearrange intersections to match Lean’s expectations.
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
      using hClosure U hUopen hxU
  -- Extract a witness `y`.
  rcases hNon with ⟨y, ⟨hyU, hyIntA⟩⟩
  -- `y ∈ A` because it lies in `interior A`.
  have hyA : y ∈ (A : Set X) := interior_subset hyIntA
  -- But `U ⊆ Aᶜ`, so `y ∈ Aᶜ`, a contradiction.
  have hyCompl : y ∈ ((A : Set X)ᶜ) := hUsub hyU
  exact hyCompl hyA