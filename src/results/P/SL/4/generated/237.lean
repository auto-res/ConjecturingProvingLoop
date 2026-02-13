

theorem frontier_compl_eq_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (Aᶜ) = frontier A := by
  -- First, rewrite both frontiers using the `closure \ interior` characterisation.
  have h₁ :
      frontier (Aᶜ) = closure (Aᶜ) \ interior (Aᶜ) := by
    simpa using
      (frontier_eq_closure_diff_interior (X := X) (A := Aᶜ))
  have h₂ :
      frontier A = closure A \ interior A := by
    simpa using
      (frontier_eq_closure_diff_interior (X := X) (A := A))
  -- Next, express `closure (Aᶜ)` and `interior (Aᶜ)` in terms of `A`.
  have h_cl :
      (closure (Aᶜ) : Set X) = (interior A)ᶜ :=
    closure_compl_eq_compl_interior (A := A)
  have h_int :
      interior (Aᶜ) = (closure A)ᶜ :=
    interior_compl_eq_compl_closure (A := A)
  -- Substitute these identities into `h₁`.
  have h₁' :
      frontier (Aᶜ) = (interior A)ᶜ \ (closure A)ᶜ := by
    simpa [h_cl, h_int] using h₁
  -- Re-express the set difference as an intersection with a complement.
  have h₁'' :
      frontier (Aᶜ) = closure A ∩ (interior A)ᶜ := by
    simpa [Set.diff_eq, Set.compl_compl, Set.inter_comm, Set.inter_left_comm]
      using h₁'
  -- Do the same for `h₂`.
  have h₂' :
      frontier A = closure A ∩ (interior A)ᶜ := by
    simpa [Set.diff_eq] using h₂
  -- Conclude by transitivity.
  simpa [h₂'] using h₁''