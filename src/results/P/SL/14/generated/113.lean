

theorem Topology.interiorClosureInterior_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  -- First, use the monotonicity of `interior` to upgrade the inclusion.
  have hInt : interior A ⊆ interior B :=
    interior_mono hAB
  -- Taking closures preserves the inclusion.
  have hClos : closure (interior A) ⊆ closure (interior B) :=
    closure_mono hInt
  -- Finally, apply monotonicity of `interior` once more.
  exact interior_mono hClos