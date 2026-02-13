

theorem interior_closure_inter_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (A : Set X)) ∩ closure (interior A) ⊆ closure A := by
  intro x hx
  exact (interior_subset : interior (closure (A : Set X)) ⊆ closure A) hx.1