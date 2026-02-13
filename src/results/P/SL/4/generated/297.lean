

theorem interior_closure_inter_subset_interior_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆ interior (closure A ∩ closure B) := by
  intro x hx
  have hsubset : closure (A ∩ B) ⊆ closure A ∩ closure B :=
    closure_inter_subset_inter_closure (A := A) (B := B)
  exact (interior_mono hsubset) hx