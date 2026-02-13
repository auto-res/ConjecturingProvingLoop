

theorem P2_nhds {X} [TopologicalSpace X] {A : Set X} : P2 A ↔ ∀ x ∈ A, interior (closure (interior A)) ∈ 𝓝 x := by
  unfold P2
  constructor
  · intro hP2 x hxA
    have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
    exact (isOpen_interior.mem_nhds hx_int)
  · intro h x hxA
    have h_nhds : interior (closure (interior A)) ∈ 𝓝 x := h x hxA
    exact mem_of_mem_nhds h_nhds

theorem P1_interior_eq_closure {X} [TopologicalSpace X] {A : Set X} : interior A = closure A → P1 A := by
  intro hEq
  intro x hxA
  have hx_cl : x ∈ (closure A : Set X) := subset_closure hxA
  have hx_int : x ∈ interior A := by
    simpa [hEq.symm] using hx_cl
  exact subset_closure hx_int