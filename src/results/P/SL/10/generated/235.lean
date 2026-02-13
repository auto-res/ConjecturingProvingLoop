

theorem Topology.interior_closure_compl_inter_interior_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (Aᶜ)) ∩ interior A = (∅ : Set X) := by
  classical
  -- Step 1: rewrite `interior (closure (Aᶜ))` using an existing lemma.
  have h₁ :
      interior (closure (Aᶜ)) = (closure (interior A))ᶜ :=
    Topology.interior_closure_compl_eq_compl_closure_interior
      (X := X) (A := A)
  -- Step 2: show that the right–hand side is empty.
  have h₂ :
      (closure (interior A))ᶜ ∩ interior A = (∅ : Set X) := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases hx with ⟨hxNot, hxInt⟩
      have hxCl : x ∈ closure (interior A) := subset_closure hxInt
      exact (hxNot hxCl).elim
    · exact Set.empty_subset _
  -- Step 3: combine the equalities.
  simpa [h₁, h₂]