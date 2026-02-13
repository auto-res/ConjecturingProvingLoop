

theorem P3_iff_closure_mem_nhds {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔ ∀ x ∈ A, closure A ∈ 𝓝 x := by
  constructor
  · intro hP3
    dsimp [Topology.P3] at hP3
    intro x hx
    have hx_int : x ∈ interior (closure A) := hP3 hx
    exact (mem_interior_iff_mem_nhds).1 hx_int
  · intro h
    dsimp [Topology.P3]
    intro x hx
    have h_nhds : closure A ∈ 𝓝 x := h x hx
    exact (mem_interior_iff_mem_nhds).2 h_nhds