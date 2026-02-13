

theorem frontier_subset_closure_compl {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (A : Set X) ⊆ closure (Aᶜ) := by
  intro x hx
  -- Reinterpret `hx` using the characterization
  -- `frontier A = closure A ∩ closure (Aᶜ)`.
  have hx_inter : x ∈ closure A ∩ closure (Aᶜ) := by
    have h_eq :=
      (closure_inter_closure_compl_eq_frontier (X := X) (A := A)).symm
    simpa [h_eq] using hx
  -- Conclude with the second component of the intersection.
  exact hx_inter.2