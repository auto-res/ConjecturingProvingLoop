

theorem frontier_inter_interior_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (A : Set X) ∩ interior A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hFront : x ∈ frontier A := hx.1
    have hInt   : x ∈ interior A := hx.2
    have hNotInt : x ∉ interior A :=
      (frontier_subset_compl_interior (X := X) (A := A)) hFront
    have : False := hNotInt hInt
    simpa using this
  · intro x hx
    cases hx