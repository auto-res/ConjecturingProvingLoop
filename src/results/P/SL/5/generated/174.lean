

theorem interior_diff_self_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior ((A : Set X) \ A) = (∅ : Set X) := by
  simp