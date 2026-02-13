

theorem Topology.P2_of_subset_closureInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B)
    (hBsubset : (B : Set X) ⊆ interior (closure (interior A))) :
    Topology.P2 B := by
  dsimp [Topology.P2] at *
  intro x hxB
  -- From the assumption, `x` lies in `interior (closure (interior A))`.
  have hxA : (x : X) ∈ interior (closure (interior A)) := hBsubset hxB
  -- We now show that
  -- `interior (closure (interior A)) ⊆ interior (closure (interior B))`.
  have h_mono :
      interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
    -- Monotonicity of `interior` with respect to set inclusion.
    have h_int : interior A ⊆ interior B := interior_mono hAB
    -- Taking closures preserves inclusion.
    have h_closure : closure (interior A) ⊆ closure (interior B) :=
      closure_mono h_int
    -- Finally, apply monotonicity of `interior` once more.
    exact interior_mono h_closure
  -- Combining the two facts yields the desired result.
  exact h_mono hxA