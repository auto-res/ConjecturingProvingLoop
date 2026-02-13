

theorem isOpen_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hx
  -- `closure A` is a neighborhood of `x`
  have h_nhds_closure : closure A ∈ 𝓝 x := by
    have h_nhdsA : A ∈ 𝓝 x := hA.mem_nhds hx
    exact Filter.mem_of_superset h_nhdsA subset_closure
  -- hence `x` belongs to the interior of `closure A`
  have h_mem_closure : x ∈ interior (closure A) :=
    (mem_interior_iff_mem_nhds).2 h_nhds_closure
  -- rewrite to obtain the desired membership
  simpa [hA.interior_eq] using h_mem_closure