

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A := by
  -- `interior A` coincides with `A` since `A` is open
  have hInt : interior A = A := hA.interior_eq
  -- an open set is contained in the interior of its closure
  have hGoal : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  -- rewrite the target using `hInt`
  have hClosEq : closure (interior A) = closure A := by
    simpa [hInt]
  have : A ⊆ interior (closure (interior A)) := by
    simpa [hClosEq] using hGoal
  exact this