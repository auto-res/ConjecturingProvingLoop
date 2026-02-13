

theorem closure_inter_eq_empty_of_disjoint_closures {X : Type*} [TopologicalSpace X]
    {A B : Set X}
    (h : closure (A : Set X) ∩ closure (B : Set X) = (∅ : Set X)) :
    closure ((A ∩ B) : Set X) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx' : (x : X) ∈ closure (A : Set X) ∩ closure (B : Set X) :=
      (closure_inter_subset_inter_closures (A := A) (B := B)) hx
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [h] using hx'
    exact this
  · exact Set.empty_subset _