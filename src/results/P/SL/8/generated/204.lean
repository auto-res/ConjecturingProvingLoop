

theorem P2_subset_closureInteriorClosureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    A ⊆ closure (interior (closure (interior A))) := by
  -- First, upgrade `P2 A` to `P1 A`.
  have hP1 : Topology.P1 A :=
    Topology.P2_imp_P1 (X := X) (A := A) hP2
  -- Then apply the established result for `P1 A`.
  exact
    P1_subset_closureInteriorClosureInterior (X := X) (A := A) hP1