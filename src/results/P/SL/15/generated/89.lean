

theorem P2_iff_closureInterior_mem_nhds {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ ∀ x ∈ A, closure (interior A) ∈ 𝓝 x := by
  classical
  constructor
  · intro hP2 x hx
    have hx_int : x ∈ interior (closure (interior A)) := hP2 hx
    exact (mem_interior_iff_mem_nhds).1 hx_int
  · intro h
    dsimp [Topology.P2]
    intro x hx
    have h_nhds : closure (interior A) ∈ 𝓝 x := h x hx
    exact (mem_interior_iff_mem_nhds).2 h_nhds