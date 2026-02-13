

theorem Topology.closure_interior_compl_eq_compl_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (Aᶜ : Set X)) = (interior (closure (A : Set X)))ᶜ := by
  -- First rewrite `interior (Aᶜ)` using the complement–closure duality.
  have h₁ :
      interior (Aᶜ : Set X) = (closure (A : Set X))ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  -- Apply `closure` to both sides and simplify using `closure_compl`.
  calc
    closure (interior (Aᶜ : Set X))
        = closure ((closure (A : Set X))ᶜ) := by
          simpa [h₁]
    _ = (interior (closure (A : Set X)))ᶜ := by
          simpa using closure_compl (s := closure (A : Set X))