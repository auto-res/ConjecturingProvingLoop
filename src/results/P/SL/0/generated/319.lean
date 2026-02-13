

theorem P2_iff_forall_open_neighborhood {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔
      ∀ x ∈ (A : Set X), ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        U ⊆ interior (closure (interior (A : Set X))) := by
  dsimp [Topology.P2]
  constructor
  · intro hP2 x hxA
    exact
      ⟨interior (closure (interior (A : Set X))), isOpen_interior,
        hP2 hxA, subset_rfl⟩
  · intro h x hxA
    rcases h x hxA with ⟨U, _hUopen, hxU, hUsub⟩
    exact hUsub hxU