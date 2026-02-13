

theorem closure_frontier_eq_closure_inter_closures {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (frontier A) = closure A ∩ closure (Aᶜ) := by
  -- `frontier A` is closed, hence its closure is itself.
  have h₁ : closure (frontier A) = frontier A :=
    closure_frontier_eq_frontier (X := X) (A := A)
  -- `frontier A` can also be expressed as the intersection of the two closures.
  have h₂ : frontier A = closure A ∩ closure (Aᶜ) :=
    (closure_inter_closure_compl_eq_frontier (X := X) (A := A)).symm
  -- Combine the two equalities.
  simpa [h₁] using h₂