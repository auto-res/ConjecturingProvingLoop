

theorem Topology.interior_closure_inter_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxIntClos, hxIntCompl⟩
    -- `x` also lies in `closure A`
    have hxClos : (x : X) ∈ closure A := interior_subset hxIntClos
    -- Hence `x` lies in the already‐known empty intersection
    have hxIn : x ∈ closure A ∩ interior (Aᶜ) :=
      And.intro hxClos hxIntCompl
    -- But this intersection is empty
    have hEmpty :
        (closure A ∩ interior (Aᶜ) : Set X) = (∅ : Set X) :=
      Topology.closure_inter_interior_compl_eq_empty (A := A)
    have : x ∈ (∅ : Set X) := by
      simpa [hEmpty] using hxIn
    cases this
  · exact Set.empty_subset _