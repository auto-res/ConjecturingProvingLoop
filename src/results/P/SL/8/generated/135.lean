

theorem P2_imp_closure_subset_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    closure A ⊆ closure (interior A) := by
  -- First, upgrade `P2 A` to `P1 A`.
  have hP1 : Topology.P1 A :=
    Topology.P2_imp_P1 (X := X) (A := A) hP2
  -- Translate `P1 A` into the desired inclusion of closures.
  exact
    (Topology.P1_iff_closure_subset_closureInterior (X := X) (A := A)).1 hP1