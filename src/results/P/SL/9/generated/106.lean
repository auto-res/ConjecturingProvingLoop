

theorem Topology.closureInteriorCompl_eq_compl_interiorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (Aᶜ)) = (interior (closure A))ᶜ := by
  -- First, rewrite `interior (Aᶜ)` using the complement–closure relation.
  have h₁ : interior (Aᶜ) = (closure A)ᶜ :=
    Topology.interior_compl_eq_compl_closure (A := A)
  -- Use `h₁` to rewrite the left‐hand side and then apply the analogous
  -- complement–interior relation to `closure A`.
  calc
    closure (interior (Aᶜ)) = closure ((closure A)ᶜ) := by
      simpa [h₁]
    _ = (interior (closure A))ᶜ := by
      simpa using
        (Topology.closure_compl_eq_compl_interior (A := closure A))