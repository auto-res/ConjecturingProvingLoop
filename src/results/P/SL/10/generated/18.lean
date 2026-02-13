

theorem Topology.P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P1 (A i)) → Topology.P1 (⋃ i, A i) := by
  intro h_all
  dsimp [Topology.P1] at h_all ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxA⟩
  have hx_cl : x ∈ closure (interior (A i)) := (h_all i) hxA
  have h_subset : closure (interior (A i)) ⊆ closure (interior (⋃ i, A i)) := by
    have h_int : interior (A i) ⊆ interior (⋃ i, A i) := by
      have h_sub : (A i) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_sub
    exact closure_mono h_int
  exact h_subset hx_cl