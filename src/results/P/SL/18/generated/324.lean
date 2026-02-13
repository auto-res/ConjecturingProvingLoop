

theorem interior_inter_closure_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    (interior (A : Set X) ∩ closure (B : Set X)) ⊆
      closure (A ∩ B : Set X) := by
  simpa [Set.inter_comm] using
    (closure_inter_interior_subset_closure_inter (A := B) (B := A))