

theorem interior_inter_self {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior ((A : Set X) ∩ A) = interior A := by
  simpa [Set.inter_self]