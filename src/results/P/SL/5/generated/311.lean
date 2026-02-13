

theorem interior_closureInterior_diff_self_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior (A : Set X)) \ A) = (∅ : Set X) := by
  classical
  apply le_antisymm
  · intro x hx
    rcases mem_interior.1 hx with ⟨U, hUsub, hUopen, hxU⟩
    -- `x` lies in the closure of `interior A`.
    have hxClInt : x ∈ closure (interior (A : Set X)) := (hUsub hxU).1
    -- Hence every open neighbourhood of `x`, in particular `U`,
    -- meets `interior A`.
    have hNon : ((U : Set X) ∩ interior (A : Set X)).Nonempty := by
      have h := (mem_closure_iff).1 hxClInt
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
        using h U hUopen hxU
    rcases hNon with ⟨y, ⟨hyU, hyIntA⟩⟩
    -- But `U` is contained in `closure (interior A) \ A`, so `y ∉ A`,
    -- contradicting `y ∈ interior A ⊆ A`.
    have hyA : y ∈ (A : Set X) := interior_subset hyIntA
    have hyNotA : y ∉ (A : Set X) := (hUsub hyU).2
    exact (hyNotA hyA).elim
  · exact Set.empty_subset _