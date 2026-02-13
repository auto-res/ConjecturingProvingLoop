

theorem Topology.interior_closure_compl_eq_compl_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (Aᶜ : Set X)) = (closure (interior (A : Set X)))ᶜ := by
  -- First, rewrite `closure (Aᶜ)` using the complement–interior duality.
  have h₁ : (closure (Aᶜ : Set X)) = (interior (A : Set X))ᶜ := by
    simpa using
      (Topology.closure_compl_eq_compl_interior (X := X) (A := A))
  -- Apply the same duality to `interior ((interior A)ᶜ)`.
  calc
    interior (closure (Aᶜ : Set X))
        = interior ((interior (A : Set X))ᶜ) := by
          simpa [h₁]
    _ = (closure (interior (A : Set X)))ᶜ := by
          simpa using
            (Topology.interior_compl_eq_compl_closure
              (X := X) (A := interior A))