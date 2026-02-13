

theorem boundary_eq_boundary_complement {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) \ interior (A : Set X) =
      closure ((Aᶜ) : Set X) \ interior ((Aᶜ) : Set X) := by
  classical
  -- Boundary of `A` described as an intersection of closures.
  have h₁ :=
    boundary_eq_closure_inter_closure_compl (A := A)
  -- Boundary of `Aᶜ` described similarly, then simplified.
  have h₂ :
      closure ((Aᶜ) : Set X) \ interior ((Aᶜ) : Set X) =
        closure ((Aᶜ) : Set X) ∩ closure (A : Set X) := by
    simpa [Set.compl_compl] using
      (boundary_eq_closure_inter_closure_compl
        (A := (Aᶜ : Set X)))
  -- Compare the two characterisations.
  calc
    closure (A : Set X) \ interior (A : Set X)
        = closure (A : Set X) ∩ closure ((Aᶜ) : Set X) := by
          simpa using h₁
    _ = closure ((Aᶜ) : Set X) ∩ closure (A : Set X) := by
          simpa [Set.inter_comm]
    _ = closure ((Aᶜ) : Set X) \ interior ((Aᶜ) : Set X) := by
          simpa using h₂.symm