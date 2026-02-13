

theorem Topology.interior_closure_interior_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  -- `interior` is monotone, so the inclusion `A ⊆ B` gives
  -- `interior A ⊆ interior B`.
  have hInt : interior A ⊆ interior B := interior_mono hAB
  -- Applying `closure` preserves inclusions.
  have hCl : closure (interior A) ⊆ closure (interior B) := closure_mono hInt
  -- Finally, use monotonicity of `interior` once more.
  exact interior_mono hCl