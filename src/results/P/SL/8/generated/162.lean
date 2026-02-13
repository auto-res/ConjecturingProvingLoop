

theorem P2_iUnion {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, Topology.P2 (A i)) :
    Topology.P2 (⋃ i, A i) := by
  dsimp [Topology.P2] at hA ⊢
  intro x hxUnion
  rcases Set.mem_iUnion.mp hxUnion with ⟨i, hxAi⟩
  -- Apply `P2` to obtain membership in the appropriate interior.
  have hxP2 : x ∈ interior (closure (interior (A i))) := (hA i) hxAi
  -- Relate the successive interiors and closures for `A i` and the union.
  have h_int_subset : interior (A i) ⊆ interior (⋃ j, A j) := by
    have h_sub : A i ⊆ ⋃ j, A j := Set.subset_iUnion _ _
    exact interior_mono h_sub
  have h_closure_subset :
      closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono h_int_subset
  have h_interior_subset :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ j, A j))) :=
    interior_mono h_closure_subset
  exact h_interior_subset hxP2