

theorem P1_subset_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → ∃ B, B ⊆ A ∧ Topology.P3 B := by
  intro _hP1
  exact ⟨(∅ : Set X), Set.empty_subset _, P3_empty (X := X)⟩

theorem P2_of_forall_nhds {X : Type*} [TopologicalSpace X] {A : Set X} : (∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ closure U ⊆ interior A) → Topology.P2 A := by
  intro h
  intro x hxA
  obtain ⟨U, hU_open, hxU, h_closure⟩ := h x hxA
  -- `U` is an open neighbourhood of `x` with `closure U ⊆ interior A`
  -- Hence `U ⊆ interior A`
  have hU_sub_int : (U : Set X) ⊆ interior A := by
    intro y hyU
    have hy_closure : (y : X) ∈ closure U := subset_closure hyU
    exact h_closure hy_closure
  -- Therefore `x ∈ interior A`
  have hx_intA : x ∈ interior A := hU_sub_int hxU
  -- `interior A ⊆ interior (closure (interior A))`
  have h_subset :
      interior A ⊆ interior (closure (interior A)) := by
    simpa [interior_interior] using
      (interior_mono
        (subset_closure : (interior A : Set X) ⊆ closure (interior A)))
  exact h_subset hx_intA