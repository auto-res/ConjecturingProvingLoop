

theorem interior_closure_diff_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (A : Set X) \ A) = (∅ : Set X) := by
  classical
  apply le_antisymm
  · intro x hx
    rcases mem_interior.1 hx with ⟨U, hUsub, hUopen, hxU⟩
    -- The point `x` lies in `closure A`, since `U ⊆ closure A \ A ⊆ closure A`.
    have hxCl : x ∈ closure (A : Set X) := by
      have : x ∈ closure (A : Set X) \ A := hUsub hxU
      exact this.1
    -- By the defining property of the closure, every open neighbourhood of `x`
    -- meets `A`, and in particular the neighbourhood `U` does.
    have hNon : ((U : Set X) ∩ A).Nonempty :=
      (mem_closure_iff).1 hxCl U hUopen hxU
    -- However, `U ⊆ closure A \ A`, so `U` is disjoint from `A`, a contradiction.
    rcases hNon with ⟨y, ⟨hyU, hyA⟩⟩
    have : y ∉ A := by
      have : y ∈ closure (A : Set X) \ A := hUsub hyU
      exact this.2
    exact (this hyA).elim
  · exact Set.empty_subset _