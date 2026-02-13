

theorem Topology.interior_inter_closure_compl_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∩ closure (Aᶜ) = (∅ : Set X) := by
  have h : closure (Aᶜ : Set X) = (interior A)ᶜ :=
    Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  calc
    interior A ∩ closure (Aᶜ) =
        interior A ∩ (interior A)ᶜ := by
          simpa [h]
    _ = (∅ : Set X) := by
          simpa [Set.inter_compl_self]