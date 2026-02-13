

theorem Topology.P3_iUnion {X ι : Type*} [TopologicalSpace X] (A : ι → Set X)
    (hA : ∀ i, Topology.P3 (X := X) (A i)) :
    Topology.P3 (X := X) (⋃ i, A i) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hx_int : x ∈ interior (closure (A i)) := hA i hxAi
  have h_sub : interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) := by
    have h_set : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    have h_closure : closure (A i : Set X) ⊆ closure (⋃ j, A j) :=
      closure_mono h_set
    exact interior_mono h_closure
  exact h_sub hx_int