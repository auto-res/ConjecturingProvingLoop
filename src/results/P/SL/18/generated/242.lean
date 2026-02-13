

theorem closure_interior_eq_univ_of_P1_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hDense : Dense (A : Set X)) :
    closure (interior (A : Set X)) = (Set.univ : Set X) := by
  classical
  -- Density of `A` gives `closure A = univ`.
  have hClosA : closure (A : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ (A := A)).1 hDense
  -- From `P1`, `closure A ⊆ closure (interior A)`.
  have hIncl : closure (A : Set X) ⊆ closure (interior (A : Set X)) :=
    Topology.closure_subset_closure_interior_of_P1 (A := A) hP1
  -- Hence `univ ⊆ closure (interior A)`.
  have hLeft : (Set.univ : Set X) ⊆ closure (interior (A : Set X)) := by
    simpa [hClosA] using hIncl
  -- Conclude the desired equality.
  apply Set.Subset.antisymm
  · intro _ _; trivial
  · exact hLeft