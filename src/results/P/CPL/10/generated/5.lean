

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure A = Set.univ) : Topology.P3 A := by
  intro x hx
  simpa [hA, isOpen_univ.interior_eq] using (Set.mem_univ x)

theorem exists_nonempty_P3 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, A.Nonempty ∧ Topology.P3 A := by
  classical
  obtain ⟨x⟩ := (‹Nonempty X›)
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact ⟨x, by simp⟩
  · simpa using (P3_of_open (A := (Set.univ : Set X)) isOpen_univ)

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {F : ι → Set X} (hF : ∀ i, Topology.P2 (F i)) : Topology.P2 (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hx_in : x ∈ interior (closure (interior (F i))) := (hF i) hxFi
  have hsubset :
      (interior (closure (interior (F i))) : Set X) ⊆
        interior (closure (interior (⋃ i, F i))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    exact Set.subset_iUnion _ i
  exact hsubset hx_in