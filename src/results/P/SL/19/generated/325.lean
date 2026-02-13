

theorem Topology.closure_interior_inter_closure_interior_compl_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∩ closure (interior (Aᶜ)) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hClosIntA, hClosIntAc⟩
  -- `x` lies in `closure A` because `closure (interior A) ⊆ closure A`.
  have hClosA : x ∈ closure A := by
    have hSub : closure (interior A) ⊆ closure A :=
      Topology.closure_interior_subset_closure (A := A)
    exact hSub hClosIntA
  -- Show that `x ∉ interior A`; otherwise we obtain a contradiction.
  have hNotIntA : x ∉ interior A := by
    intro hxIntA
    -- `interior A` is an open neighbourhood of `x`; since
    -- `x ∈ closure (interior (Aᶜ))`, this neighbourhood meets `interior (Aᶜ)`.
    have hNon :
        ((interior A : Set X) ∩ interior (Aᶜ)).Nonempty :=
      (mem_closure_iff).1 hClosIntAc (interior A) isOpen_interior hxIntA
    rcases hNon with ⟨y, ⟨hyIntA, hyIntAc⟩⟩
    -- But a point cannot belong to both `A` and `Aᶜ`.
    have hInA  : (y : X) ∈ A   := interior_subset hyIntA
    have hInAc : (y : X) ∈ Aᶜ := interior_subset hyIntAc
    exact (hInAc hInA)
  exact And.intro hClosA hNotIntA