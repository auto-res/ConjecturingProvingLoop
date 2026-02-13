

theorem Topology.P1_iUnion {ι X : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hP : ∀ i, Topology.P1 (X := X) (A i)) :
    Topology.P1 (X := X) (⋃ i, A i) := by
  classical
  dsimp [Topology.P1] at hP ⊢
  intro x hxUnion
  rcases Set.mem_iUnion.1 hxUnion with ⟨i, hxAi⟩
  have hx_cl : x ∈ closure (interior (A i)) := (hP i) hxAi
  have h_subset : interior (A i) ⊆ interior (⋃ j, A j) := by
    -- `interior (A i)` is open and contained in the union
    have h_open : IsOpen (interior (A i)) := isOpen_interior
    have h_sub : interior (A i) ⊆ ⋃ j, A j := by
      intro y hy
      have hyAi : y ∈ A i := interior_subset hy
      exact Set.mem_iUnion.2 ⟨i, hyAi⟩
    exact interior_maximal h_sub h_open
  have h_closure_subset :
      closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono h_subset
  exact h_closure_subset hx_cl