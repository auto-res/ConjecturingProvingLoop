

theorem interior_diff_interior_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior ((A : Set X) \ interior A) = (∅ : Set X) := by
  classical
  apply le_antisymm
  · intro x hx
    rcases mem_interior.1 hx with ⟨U, hUsub, hUopen, hxU⟩
    -- `U` is an open subset of `A`.
    have hU_sub_A : (U : Set X) ⊆ A := by
      intro y hy
      exact (hUsub hy).1
    -- By maximality of the interior, `U ⊆ interior A`.
    have hU_sub_intA : (U : Set X) ⊆ interior (A : Set X) :=
      interior_maximal hU_sub_A hUopen
    -- Hence `x ∈ interior A`.
    have hx_intA : x ∈ interior (A : Set X) := hU_sub_intA hxU
    -- But `x ∉ interior A`, since `x ∈ A \ interior A`.
    have hx_not_intA : x ∉ interior (A : Set X) := (hUsub hxU).2
    exact (hx_not_intA hx_intA).elim
  · exact Set.empty_subset _