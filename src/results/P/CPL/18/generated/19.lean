

theorem exists_closed_subset_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ F : Set X, IsClosed F ∧ F ⊆ A ∧ Topology.P2 F := by
  refine ⟨(∅ : Set X), isClosed_empty, ?_, ?_⟩
  · exact Set.empty_subset _
  · simpa using (P2_empty (X := X))

theorem P1_bUnion {X ι : Type*} [TopologicalSpace X] {s : Set ι} {A : ι → Set X} (hA : ∀ i ∈ s, Topology.P1 (A i)) : Topology.P1 (⋃ i ∈ s, A i) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨his, hxAi⟩
  have hP1i : Topology.P1 (A i) := hA i his
  have hx' : x ∈ closure (interior (A i)) := hP1i hxAi
  have hsubset : closure (interior (A i)) ⊆ closure (interior (⋃ j ∈ s, A j)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    -- Show that `y` belongs to the big union.
    have : y ∈ ⋃ j ∈ s, A j := by
      apply Set.mem_iUnion.2
      exact ⟨i, Set.mem_iUnion.2 ⟨his, hy⟩⟩
    exact this
  exact hsubset hx'

theorem P1_union_compl {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (A ∪ Aᶜ) := by
  simpa [Set.union_compl_self] using (P1_univ (X := X))