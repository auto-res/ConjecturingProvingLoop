

theorem Topology.P3_of_closure_interior_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (Set.univ : Set X) → Topology.P3 A := by
  intro hClIntEq
  intro x _
  -- First, note that `interior (closure (interior A)) = univ`.
  have hIntEq : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [hClIntEq, interior_univ] using congrArg interior hClIntEq
  -- Hence every point lies in `interior (closure (interior A))`.
  have hxInt : x ∈ interior (closure (interior A)) := by
    simpa [hIntEq] using (by simp : x ∈ (Set.univ : Set X))
  -- Use monotonicity to pass to `interior (closure A)`.
  have hsubset :
      interior (closure (interior A)) ⊆ interior (closure (A : Set X)) :=
    Topology.interior_closure_interior_subset_interior_closure (A := A)
  exact hsubset hxInt