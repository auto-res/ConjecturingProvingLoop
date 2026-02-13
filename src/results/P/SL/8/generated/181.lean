

theorem P3_imp_closure_subset_closureInteriorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) :
    closure A ⊆ closure (interior (closure A)) := by
  -- First, upgrade `P3 A` to `P1 (closure A)`.
  have hP1 : Topology.P1 (closure A) :=
    Topology.P3_imp_P1_closure (X := X) (A := A) hP3
  -- Unfold the definition of `P1` for `closure A` and use it directly.
  dsimp [Topology.P1] at hP1
  simpa using hP1