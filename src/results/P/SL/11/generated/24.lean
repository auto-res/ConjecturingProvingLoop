

theorem P1_of_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- We first establish the necessary subset relation.
  have hsubset : closure (interior A) ⊆ closure (interior (closure (interior A))) := by
    apply closure_mono
    -- Since `interior A` is an open subset of `closure (interior A)`,
    -- it is contained in the interior of that closure.
    have : (interior A : Set X) ⊆ interior (closure (interior A)) := by
      apply interior_maximal
      · exact subset_closure
      · exact isOpen_interior
    exact this
  exact hsubset hx