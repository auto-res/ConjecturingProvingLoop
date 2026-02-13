

theorem Topology.interior_closure_compl_eq_compl_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (Aᶜ)) = (closure (interior A))ᶜ := by
  -- First, rewrite `closure (Aᶜ)` using the complement–interior relation.
  have h₁ := Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  -- Chain equalities, finishing with the complement–closure relation for `interior A`.
  calc
    interior (closure (Aᶜ))
        = interior ((interior A)ᶜ) := by
          simpa [h₁]
    _ = (closure (interior A))ᶜ := by
          simpa using
            (Topology.interior_compl_eq_compl_closure
              (X := X) (A := interior A))