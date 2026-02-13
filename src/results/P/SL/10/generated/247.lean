

theorem Topology.closure_interior_compl_inter_interior_closure_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (Aᶜ)) ∩ interior (closure A) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hContr : False := by
      rcases hx with ⟨hxClIntCompl, hxIntClA⟩
      -- `interior (closure A)` is an open neighbourhood of `x`.
      have hOpen : IsOpen (interior (closure A)) := isOpen_interior
      -- Hence it meets `interior (Aᶜ)`.
      have hNonempty :
          ((interior (closure A)) ∩ interior (Aᶜ)).Nonempty :=
        (mem_closure_iff).1 hxClIntCompl (interior (closure A)) hOpen hxIntClA
      rcases hNonempty with ⟨y, ⟨hyIntClA, hyIntCompl⟩⟩
      -- But `interior (closure A) ⊆ closure A`.
      have hyClA : y ∈ closure A := interior_subset hyIntClA
      -- This contradicts `closure A ∩ interior (Aᶜ) = ∅`.
      have hEmpty :=
        Topology.closure_inter_interior_compl_eq_empty (X := X) (A := A)
      have : y ∈ (∅ : Set X) := by
        simpa [hEmpty] using And.intro hyClA hyIntCompl
      exact this
    exact (False.elim hContr)
  · exact Set.empty_subset _