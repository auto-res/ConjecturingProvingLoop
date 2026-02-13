

theorem interior_inter_closure_eq_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A : Set X) ∩ closure A = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hxInt
    have hxA : x ∈ (A : Set X) := interior_subset hxInt
    have hxCl : x ∈ closure (A : Set X) := subset_closure hxA
    exact ⟨hxInt, hxCl⟩