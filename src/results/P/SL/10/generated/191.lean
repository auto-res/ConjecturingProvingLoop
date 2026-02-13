

theorem Topology.closure_diff_interior_eq_closure_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A \ interior A = closure A ∩ closure (Aᶜ) := by
  classical
  have h : closure (Aᶜ) = (interior A)ᶜ :=
    Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  calc
    closure A \ interior A
        = closure A ∩ (interior A)ᶜ := by
          simp [Set.diff_eq]
    _ = closure A ∩ closure (Aᶜ) := by
          simpa [h]