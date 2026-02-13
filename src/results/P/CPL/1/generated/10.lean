

theorem P3_iff_nhds_within {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A ↔ ∀ x ∈ A, interior (closure A) ∈ 𝓝 x := by
  refine ⟨?forward, ?backward⟩
  · intro hP3 x hx
    have hx_int : x ∈ interior (closure A) := hP3 hx
    exact (isOpen_interior).mem_nhds hx_int
  · intro h x hx
    exact mem_of_mem_nhds (h x hx)