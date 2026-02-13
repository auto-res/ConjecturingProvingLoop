

theorem Topology.closureInterior_union_eq_closure_union_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) =
      closure (interior A ∪ interior B) := by
  simpa using (closure_union (interior A) (interior B)).symm