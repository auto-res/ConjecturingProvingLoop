

theorem interior_inter_closure_compl_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∩ closure ((A : Set X)ᶜ) = (∅ : Set X) := by
  classical
  -- We show that the intersection contains no points.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hxInt, hxCl⟩
  -- Pick an open neighborhood `U` of `x` contained in `A`.
  rcases mem_interior.1 hxInt with ⟨U, hUsubA, hUopen, hxU⟩
  -- Because `x ∈ closure (Aᶜ)`, the neighborhood `U` meets `Aᶜ`.
  have hNon : ((U : Set X) ∩ ((A : Set X)ᶜ)).Nonempty :=
    (mem_closure_iff).1 hxCl U hUopen hxU
  rcases hNon with ⟨y, ⟨hyU, hyCompl⟩⟩
  -- But `U ⊆ A`, so `y ∈ A`, contradicting `y ∈ Aᶜ`.
  exact hyCompl (hUsubA hyU)