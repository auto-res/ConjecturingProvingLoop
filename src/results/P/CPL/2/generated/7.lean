

theorem P1_univ {X : Type*} [TopologicalSpace X] : Topology.P1 (X:=X) (Set.univ : Set X) := by
  unfold Topology.P1
  simpa [interior_univ, closure_univ]

theorem P2_empty {X : Type*} [TopologicalSpace X] : Topology.P2 (X:=X) (∅ : Set X) := by
  unfold Topology.P2
  intro x hx
  cases hx

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (X:=X) (interior A) := by
  unfold Topology.P1
  simpa using (subset_closure : (interior A : Set X) ⊆ closure (interior A))