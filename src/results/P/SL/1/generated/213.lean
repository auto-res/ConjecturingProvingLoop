

theorem Topology.P2_of_between
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B)
    (hBsubset : B ⊆ interior (closure (interior A))) :
    Topology.P2 B := by
  dsimp [Topology.P2] at *
  intro x hxB
  -- Step 1: upgrade `x ∈ B` to `x ∈ interior (closure (interior A))`.
  have hxIntA : x ∈ interior (closure (interior A)) := hBsubset hxB
  -- Step 2: use monotonicity of `interior ∘ closure ∘ interior`
  -- with the inclusion `A ⊆ B`.
  have hmono :
      interior (closure (interior A)) ⊆
        interior (closure (interior B)) :=
    Topology.interior_closure_interior_mono (A := A) (B := B) hAB
  exact hmono hxIntA