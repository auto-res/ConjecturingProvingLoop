

theorem interior_union_closure_complement {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∪ closure ((Aᶜ) : Set X) = (Set.univ : Set X) := by
  classical
  -- We prove the equality by showing mutual inclusion.
  apply Set.Subset.antisymm
  · -- The union is obviously contained in `univ`.
    intro x hx
    cases hx with
    | inl _ => exact Set.mem_univ _
    | inr _ => exact Set.mem_univ _
  · -- Conversely, every point of `univ` belongs to the union.
    intro x _
    by_cases hx : (x : X) ∈ interior (A : Set X)
    · -- If `x ∈ interior A`, we are done.
      exact Or.inl hx
    · -- Otherwise, use `closure (Aᶜ) = (interior A)ᶜ`.
      have hEq := closure_compl_eq_complement_interior (A := A)
      have : (x : X) ∈ closure ((Aᶜ) : Set X) := by
        have : (x : X) ∈ (interior (A : Set X))ᶜ := by
          simp [hx]
        simpa [hEq] using this
      exact Or.inr this