

theorem Topology.closure_interior_union_interior_closure_compl_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∪ interior (closure (Aᶜ)) = (Set.univ : Set X) := by
  have h :
      interior (closure (Aᶜ)) = (closure (interior A))ᶜ :=
    Topology.interior_closure_compl_eq_compl_closure_interior (X := X) (A := A)
  calc
    closure (interior A) ∪ interior (closure (Aᶜ))
        = closure (interior A) ∪ (closure (interior A))ᶜ := by
          simpa [h]
    _ = (Set.univ : Set X) := by
          simpa [Set.union_compl_self]