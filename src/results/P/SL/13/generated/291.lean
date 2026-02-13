

theorem Topology.boundary_eq_closure_inter_closureCompl {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) \ interior A =
      closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
  -- Relate `closure (Aᶜ)` to the complement of `interior A`.
  have h :
      closure (Aᶜ : Set X) = (interior (A : Set X))ᶜ :=
    Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  -- Rewrite the boundary in two steps.
  calc
    closure (A : Set X) \ interior A
        = closure (A : Set X) ∩ (interior (A : Set X))ᶜ := by
          simpa [Set.diff_eq]
    _ = closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
          simpa [h]