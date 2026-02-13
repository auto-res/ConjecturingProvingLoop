

theorem Topology.closureInteriorClosureInterior_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    closure (interior (closure (interior A))) ⊆
      closure (interior (closure (interior B))) := by
  exact
    closure_mono
      (interior_mono
        (closure_mono
          (interior_mono hAB)))