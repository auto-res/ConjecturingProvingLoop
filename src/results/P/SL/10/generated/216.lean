

theorem Topology.interior_closure_union_closure_interior_compl_eq_univ
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure A) ∪ closure (interior (Aᶜ)) = (Set.univ : Set X) := by
  have h :
      closure (interior (Aᶜ)) = (interior (closure A))ᶜ :=
    Topology.closure_interior_compl_eq_compl_interior_closure
      (X := X) (A := A)
  calc
    interior (closure A) ∪ closure (interior (Aᶜ))
        = interior (closure A) ∪ (interior (closure A))ᶜ := by
          simpa [h]
    _ = (Set.univ : Set X) := by
          simpa [Set.union_compl_self]