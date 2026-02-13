

theorem Topology.interior_frontier_eq_empty_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    interior (frontier (A : Set X)) = (∅ : Set X) := by
  classical
  -- First, rewrite the frontier of an open set.
  have h_front : frontier (A : Set X) = closure A \ A :=
    Topology.frontier_eq_closure_diff_self_of_isOpen (A := A) hA
  -- We show that the interior of `closure A \ A` is empty.
  have h_empty : interior (closure A \ A) = (∅ : Set X) := by
    apply (Set.eq_empty_iff_forall_not_mem).2
    intro x hx_int
    -- Obtain an open neighbourhood `U` of `x` contained in `closure A \ A`.
    rcases (mem_interior).1 hx_int with ⟨U, hU_sub, hU_open, hxU⟩
    -- Since `x ∈ interior (closure A \ A)`, it certainly lies in `closure A`.
    have hx_closureA : x ∈ closure (A : Set X) := by
      have : x ∈ closure A \ A :=
        (interior_subset : interior (closure A \ A) ⊆ closure A \ A) hx_int
      exact this.1
    -- Every neighbourhood of `x` meets `A`; apply this to `U`.
    have h_nonempty : (U ∩ A).Nonempty :=
      (mem_closure_iff).1 hx_closureA U hU_open hxU
    rcases h_nonempty with ⟨y, ⟨hyU, hyA⟩⟩
    -- But `U` is contained in `closure A \ A`, so `y ∉ A`, a contradiction.
    have hy_notA : y ∉ A := (hU_sub hyU).2
    exact hy_notA hyA
  -- Substitute back to finish the proof.
  simpa [h_front, h_empty]