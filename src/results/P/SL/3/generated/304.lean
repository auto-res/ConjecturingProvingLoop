

theorem closure_eq_interior_iff_boundary_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) = interior (A : Set X) ↔
      closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) := by
  classical
  constructor
  · intro hEq
    simpa [hEq, Set.diff_self]
  · intro hEmpty
    apply Set.Subset.antisymm
    · intro x hxCl
      by_cases hxInt : (x : X) ∈ interior (A : Set X)
      · exact hxInt
      ·
        have hxDiff :
            (x : X) ∈ closure (A : Set X) \ interior (A : Set X) :=
          And.intro hxCl hxInt
        have : (x : X) ∈ (∅ : Set X) := by
          simpa [hEmpty] using hxDiff
        cases this
    · intro x hxInt
      exact subset_closure (interior_subset hxInt)