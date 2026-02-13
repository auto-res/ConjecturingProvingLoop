

theorem interior_closure_union_closure_complement {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (A : Set X)) ∪ closure ((Aᶜ) : Set X) =
      (Set.univ : Set X) := by
  classical
  -- A handy rewriting of `closure (Aᶜ)`.
  have hEq : closure ((Aᶜ) : Set X) = (interior (A : Set X))ᶜ :=
    closure_compl_eq_complement_interior (A := A)
  -- Prove the equality by double inclusion.
  apply Set.Subset.antisymm
  · intro x _; exact Set.mem_univ x
  · intro x _
    by_cases hInt : (x : X) ∈ interior (A : Set X)
    · -- `x ∈ interior A` ⇒ `x ∈ interior (closure A)`.
      have hIncl : interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
        interior_subset_interior_closure (A := A)
      exact Or.inl (hIncl hInt)
    · -- Otherwise, `x ∈ (interior A)ᶜ = closure (Aᶜ)`.
      have hxCompl : (x : X) ∈ (interior (A : Set X))ᶜ := by
        simp [hInt]
      have hxCl : (x : X) ∈ closure ((Aᶜ) : Set X) := by
        simpa [hEq] using hxCompl
      exact Or.inr hxCl