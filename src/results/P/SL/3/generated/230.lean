

theorem P1_iff_closure_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A : Set X) ↔
      closure (A : Set X) ⊆ closure (interior (A : Set X)) := by
  constructor
  · intro hP1
    exact closure_subset_closure_interior_of_P1 (A := A) hP1
  · intro hSub
    -- The reverse inclusion is always true.
    have hSup : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset (s := A))
    -- Hence we have equality of the two closures.
    have hEq : closure (A : Set X) = closure (interior (A : Set X)) :=
      Set.Subset.antisymm hSub hSup
    -- Use the existing equivalence with this equality.
    have hP1 :=
      (P1_iff_closure_eq_closure_interior (A := A)).mpr hEq
    exact hP1