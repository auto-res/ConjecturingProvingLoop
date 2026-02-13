

theorem Topology.P2_implies_eq_empty_of_empty_interior_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → interior (closure (interior A)) = ∅ → A = (∅ : Set X) := by
  intro hP2 hIntEq
  -- Show `A ⊆ ∅`
  have hSub : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hxA
    have : (x : X) ∈ interior (closure (interior A)) := hP2 hxA
    simpa [hIntEq] using this
  -- The reverse inclusion is trivial.
  have hSub' : (∅ : Set X) ⊆ (A : Set X) := by
    intro x hx
    cases hx
  exact subset_antisymm hSub hSub'