

theorem frontier_inter_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (A : Set X) ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxFront : x ∈ frontier A := hx.1
    have hxIntComp : x ∈ interior (Aᶜ) := hx.2
    -- `interior (Aᶜ)` is the complement of `closure A`
    have hIntEq : interior (Aᶜ : Set X) = (closure A)ᶜ :=
      interior_compl_eq_compl_closure (A := A)
    have hxNotClosure : x ∉ closure A := by
      have : x ∈ (closure A)ᶜ := by
        simpa [hIntEq] using hxIntComp
      exact this
    have hxClosure : x ∈ closure A := hxFront.1
    have hFalse : False := hxNotClosure hxClosure
    exact False.elim hFalse
  · exact Set.empty_subset _