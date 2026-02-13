

theorem Topology.interior_closure_compl_inter_closure_interior_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (Aᶜ)) ∩ closure (interior A) = (∅ : Set X) := by
  have h :
      interior (closure (Aᶜ)) = (closure (interior A))ᶜ :=
    Topology.interior_closure_compl_eq_compl_closure_interior (X := X) (A := A)
  calc
    interior (closure (Aᶜ)) ∩ closure (interior A)
        = (closure (interior A))ᶜ ∩ closure (interior A) := by
          simpa [h]
    _ = (∅ : Set X) := by
          simpa [Set.inter_compl_self]