

theorem interior_inter_closure_eq_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A : Set X) ∩ closure (A : Set X) = interior (A : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.1
  · intro x hx
    exact And.intro hx (interior_subset_closure_self (A := A) hx)