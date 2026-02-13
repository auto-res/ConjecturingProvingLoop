

theorem Topology.P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, Topology.P2 (A i)) : Topology.P2 (⋃ i, A i) := by
  dsimp [Topology.P2] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx_int : x ∈ interior (closure (interior (A i))) := (hA i) hxi
  have h_mono :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ j, A j))) := by
    have h_closure_mono :
        closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
      have h_int_mono :
          interior (A i) ⊆ interior (⋃ j, A j) := by
        have h_subset : (A i : Set X) ⊆ ⋃ j, A j := by
          intro y hy
          exact Set.mem_iUnion.2 ⟨i, hy⟩
        exact interior_mono h_subset
      exact closure_mono h_int_mono
    exact interior_mono h_closure_mono
  exact h_mono hx_int