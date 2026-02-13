

theorem Topology.dense_isClosed_implies_frontier_eq_empty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Dense A → IsClosed A → frontier (A : Set X) = (∅ : Set X) := by
  intro hDense hClosed
  have hA : (A : Set X) = (Set.univ : Set X) :=
    Topology.dense_isClosed_implies_univ (A := A) hDense hClosed
  simpa [hA, frontier_univ]