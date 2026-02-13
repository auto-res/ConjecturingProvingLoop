

theorem Topology.P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P3 (A i)) → Topology.P3 (⋃ i, A i) := by
  intro h_all
  dsimp [Topology.P3] at h_all ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxA⟩
  have hx_int : x ∈ interior (closure (A i)) := (h_all i) hxA
  have h_subset : interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) := by
    have h_closure : closure (A i) ⊆ closure (⋃ j, A j) := by
      have h_sub : (A i) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono h_sub
    exact interior_mono h_closure
  exact h_subset hx_int