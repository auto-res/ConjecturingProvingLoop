

theorem P1_Union {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, Topology.P1 (X:=X) (A i)) : Topology.P1 (X:=X) (⋃ i, A i) := by
  classical
  -- Unpack the definition of `P1`
  unfold Topology.P1 at h ⊢
  intro x hx
  -- Choose an index `i` with `x ∈ A i`
  rcases (Set.mem_iUnion).1 hx with ⟨i, hxAi⟩
  -- Apply `P1` for this particular `i`
  have hx₁ : x ∈ closure (interior (A i)) := h i hxAi
  -- Show the required inclusion of closures
  have h_subset :
      closure (interior (A i)) ⊆
        closure (interior (⋃ j, A j)) := by
    apply closure_mono
    have h_int_subset :
        interior (A i) ⊆ interior (⋃ j, A j) := by
      apply interior_mono
      intro y hy
      exact Set.mem_iUnion_of_mem i hy
    exact h_int_subset
  -- Conclude
  exact h_subset hx₁

theorem P2_univ {X : Type*} [TopologicalSpace X] : Topology.P2 (X:=X) (Set.univ : Set X) := by
  unfold Topology.P2
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_empty {X : Type*} [TopologicalSpace X] : Topology.P3 (X:=X) (∅ : Set X) := by
  unfold Topology.P3
  intro x hx
  cases hx

theorem closure_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P1 (X:=X) A) : closure A ⊆ closure (interior A) := by
  simpa using closure_mono h

theorem exists_compact_P2 {X : Type*} [TopologicalSpace X] [CompactSpace X] : ∃ A : Set X, IsCompact A ∧ Topology.P2 (X:=X) A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using isCompact_univ
  · simpa using (P2_univ (X := X))