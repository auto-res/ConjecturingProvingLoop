

theorem interior_closure_inter_comm {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    interior (closure (A ∩ B : Set X)) =
      interior (closure (B ∩ A : Set X)) := by
  simpa [Set.inter_comm]