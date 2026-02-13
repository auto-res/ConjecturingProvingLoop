

theorem Topology.interiorClosureInterior_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  -- `interior` is monotone with respect to set inclusion.
  have h₁ : interior A ⊆ interior B := interior_mono hAB
  -- `closure` preserves inclusions.
  have h₂ : closure (interior A) ⊆ closure (interior B) :=
    closure_mono h₁
  -- Applying monotonicity of `interior` once more yields the desired result.
  exact interior_mono h₂