

theorem Topology.interiorClosureInterior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  exact interior_mono (closure_mono (interior_mono hAB))