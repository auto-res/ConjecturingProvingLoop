

theorem interior_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A : Set X) ⊆ closure (interior (closure A)) := by
  intro x hxIntA
  -- Step 1: `x ∈ interior (closure A)` since `A ⊆ closure A`.
  have hxIntCl : x ∈ interior (closure (A : Set X)) :=
    (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hxIntA
  -- Step 2: `interior (closure A) ⊆ closure (interior (closure A))`.
  have h_sub : interior (closure (A : Set X)) ⊆
      closure (interior (closure (A : Set X))) :=
    subset_closure
  -- Combine the two steps.
  exact h_sub hxIntCl