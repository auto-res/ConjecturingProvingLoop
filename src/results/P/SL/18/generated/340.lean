

theorem closure_interior_inter_subset_closures_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∩ B) ⊆ closure A ∩ closure B := by
  have h :
      closure (B ∩ interior (A : Set X)) ⊆ closure B ∩ closure A :=
    closure_inter_interior_subset_closures (A := B) (B := A)
  simpa [Set.inter_comm] using h