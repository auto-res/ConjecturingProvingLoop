

theorem P2_closure_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P3]
  intro x hxA
  -- `x` belongs to the closure of `A`
  have hx_closure : x ∈ closure A := subset_closure hxA
  -- Apply `P2` for `closure A`
  have hx_int₁ : x ∈ interior (closure (interior (closure A))) := hP2 hx_closure
  -- Relate the two interiors of closures
  have h_subset :
      interior (closure (interior (closure A))) ⊆ interior (closure A) := by
    have h₁ :
        interior (closure (interior (closure A))) ⊆
          interior (closure (closure A)) :=
      interior_closure_interior_subset_interior_closure (X := X) (A := closure A)
    simpa [closure_closure] using h₁
  -- Conclude that `x` is in `interior (closure A)`
  exact h_subset hx_int₁