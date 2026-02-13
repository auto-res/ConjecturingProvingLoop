

theorem isOpen_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hxA
  -- Rewrite `interior A` using the openness of `A`
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hxA
  -- Any point of `interior A` lies in `closure (interior A)`
  exact subset_closure hx_int