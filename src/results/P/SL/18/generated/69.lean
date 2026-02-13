

theorem P1_closure_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) : Topology.P1 (closure (A : Set X)) := by
  dsimp [Topology.P1]
  have hIncl : (closure A : Set X) ⊆ closure (interior (closure A)) := by
    -- First, an open set is contained in the interior of its closure.
    have hSub : (A : Set X) ⊆ interior (closure A) :=
      interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA
    -- Taking closures preserves inclusions.
    exact closure_mono hSub
  exact hIncl