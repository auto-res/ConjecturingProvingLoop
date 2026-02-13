

theorem interior_closure_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (A : Set X))) ⊆ interior (closure (A : Set X)) := by
  have hcl : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  exact interior_mono hcl