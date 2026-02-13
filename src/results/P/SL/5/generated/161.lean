

theorem interior_eq_empty_of_closure_interior_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior (A : Set X)) = (∅ : Set X)) :
    interior (A : Set X) = (∅ : Set X) := by
  -- First, show `interior A ⊆ ∅`.
  have hsub : interior (A : Set X) ⊆ (∅ : Set X) := by
    intro x hx
    -- Any point of `interior A` lies in `closure (interior A)`.
    have hx' : x ∈ closure (interior (A : Set X)) := subset_closure hx
    -- Rewrite using the hypothesis that this closure is empty.
    simpa [h] using hx'
  -- The reverse inclusion `∅ ⊆ interior A` is trivial.
  exact le_antisymm hsub (Set.empty_subset _)