

theorem closure_interior_inter_interior_complement_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ∩ interior ((Aᶜ) : Set X) = (∅ : Set X) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxClInt, hxIntCompl⟩
    -- The open set `interior (Aᶜ)` contains `x`, so it must meet `interior A`
    -- since `x` lies in the closure of `interior A`.
    have hNonempty :
        ((interior ((Aᶜ) : Set X)) ∩ interior (A : Set X)).Nonempty :=
      (mem_closure_iff).1 hxClInt _ isOpen_interior hxIntCompl
    rcases hNonempty with ⟨y, ⟨hyIntCompl, hyIntA⟩⟩
    have hyA : (y : X) ∈ (A : Set X) := interior_subset hyIntA
    have hyAc : (y : X) ∈ ((Aᶜ) : Set X) := interior_subset hyIntCompl
    have : False := hyAc hyA
    cases this
  · exact Set.empty_subset _