

theorem P1_closed_of_P3 {X} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 A → P1 A := by
  intro hP3
  have hP2 : P2 A := (P2_iff_P3_of_closed hA).mpr hP3
  exact P1_of_P2 hP2

theorem exists_P3_subset {X} [TopologicalSpace X] {A : Set X} : ∃ B, B ⊆ A ∧ P3 B := by
  refine ⟨(∅ : Set X), Set.empty_subset _, ?_⟩
  exact P3_empty

theorem P3_iff_nhds {X} [TopologicalSpace X] {A : Set X} : P3 A ↔ ∀ x ∈ A, (closure A : Set X) ∈ 𝓝 x := by
  unfold P3
  constructor
  · intro hP3 x hxA
    have hx_int : x ∈ interior (closure A) := hP3 hxA
    exact (mem_interior_iff_mem_nhds).1 hx_int
  · intro h x hxA
    have h_nhds : (closure A : Set X) ∈ 𝓝 x := h x hxA
    exact (mem_interior_iff_mem_nhds).2 h_nhds