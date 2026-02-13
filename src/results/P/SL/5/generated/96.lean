

theorem interior_closure_inter_subset_interior_inter_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B : Set X)) ⊆ interior (closure A ∩ closure B) := by
  intro x hx
  have hsubset : closure (A ∩ B : Set X) ⊆ closure A ∩ closure B :=
    closure_inter_subset (X := X) (A := A) (B := B)
  exact (interior_mono hsubset) hx