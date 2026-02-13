

theorem P1_iff_closure_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (X:=X) A ↔ closure A ⊆ closure (interior A) := by
  unfold Topology.P1
  constructor
  · intro h
    simpa [closure_closure] using (closure_mono h)
  · intro h
    exact subset_trans (subset_closure : (A : Set X) ⊆ closure A) h

theorem exists_closed_P1 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, IsClosed A ∧ Topology.P1 (X:=X) A := by
  refine ⟨(Set.univ : Set X), isClosed_univ, ?_⟩
  simpa using (P1_univ (X := X))