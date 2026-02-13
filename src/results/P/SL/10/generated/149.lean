

theorem Topology.interior_closure_inter_closure_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure A) ∩ closure (interior (Aᶜ)) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxIntClA, hxClIntCompl⟩
    -- `interior (closure A)` is an open neighbourhood of `x`.
    have hOpen : IsOpen (interior (closure A)) := isOpen_interior
    -- Since `x ∈ closure (interior (Aᶜ))`, this neighbourhood meets `interior (Aᶜ)`.
    rcases
        (mem_closure_iff).1 hxClIntCompl (interior (closure A)) hOpen hxIntClA
      with ⟨y, ⟨hyIntClA, hyIntCompl⟩⟩
    -- But `interior (closure A) ⊆ closure A`.
    have hyClA : y ∈ closure A := interior_subset hyIntClA
    -- Hence `y ∈ closure A ∩ interior (Aᶜ)`, contradicting
    -- `closure A ∩ interior (Aᶜ) = ∅`.
    have hFalse : False := by
      have hEmpty :=
        Topology.closure_inter_interior_compl_eq_empty (X := X) (A := A)
      have : y ∈ (∅ : Set X) := by
        simpa [hEmpty] using And.intro hyClA hyIntCompl
      simpa using this
    exact False.elim hFalse
  · exact Set.empty_subset _