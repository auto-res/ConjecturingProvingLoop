

theorem Topology.interior_closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  -- First, enlarge the innermost interiors using the inclusion `A ⊆ B`.
  have hInt : (interior A : Set X) ⊆ interior B := interior_mono hAB
  -- Taking closures preserves inclusions.
  have hCl : (closure (interior A) : Set X) ⊆ closure (interior B) :=
    closure_mono hInt
  -- Finally, taking interiors preserves inclusions once more.
  exact interior_mono hCl