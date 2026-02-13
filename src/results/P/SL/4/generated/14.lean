

theorem isOpen_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hxA
  have h_int_eq : interior A = A := hA.interior_eq
  -- `interior A ⊆ interior (closure A)` by monotonicity of `interior`
  have h_sub : A ⊆ interior (closure A) := by
    have hIntSubset : interior A ⊆ interior (closure A) :=
      interior_mono subset_closure
    simpa [h_int_eq] using hIntSubset
  -- Apply the inclusion to the given point `x`
  have hx_int : x ∈ interior (closure A) := h_sub hxA
  -- Rewrite `interior (closure (interior A))` using `h_int_eq`
  simpa [h_int_eq] using hx_int