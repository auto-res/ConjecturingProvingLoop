

theorem closure_inter_closure_compl_eq_closure_diff_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ∩ closure ((A : Set X)ᶜ) =
      closure (A : Set X) \ interior A := by
  classical
  -- Rewrite the closure of the complement via the interior.
  have h :
      closure ((A : Set X)ᶜ) = (interior (A : Set X))ᶜ :=
    closure_compl_eq_compl_interior (X := X) (A := A)
  -- Substitute this equality and use the definition of set difference.
  calc
    closure (A : Set X) ∩ closure ((A : Set X)ᶜ)
        = closure (A : Set X) ∩ (interior (A : Set X))ᶜ := by
          simpa [h]
    _ = closure (A : Set X) \ interior A := by
          simpa [Set.diff_eq, Set.inter_comm]