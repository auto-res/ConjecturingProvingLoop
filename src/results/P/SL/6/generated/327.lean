

theorem interior_eq_univ_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) = (Set.univ : Set X) → Topology.P2 A := by
  intro hInt
  dsimp [Topology.P2]
  intro x _hxA
  have hIntCl :
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    simpa [hInt, closure_univ, interior_univ]
  have hx : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hIntCl] using hx