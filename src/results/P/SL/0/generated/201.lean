

theorem closure_inter_interior_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (closure (A : Set X) ∩ interior (A : Set X)) = interior (A : Set X) := by
  ext x
  constructor
  · intro h
    exact h.2
  · intro hxInt
    have hxCl : x ∈ closure (A : Set X) := by
      have hxA : x ∈ (A : Set X) := interior_subset hxInt
      exact subset_closure hxA
    exact And.intro hxCl hxInt