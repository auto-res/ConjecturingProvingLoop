

theorem Topology.closure_union_interiors_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B) = closure (interior A) ∪ closure (interior B) := by
  simpa using closure_union (s := interior A) (t := interior B)