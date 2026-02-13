

theorem Topology.P1_implies_eq_empty_of_empty_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → interior A = ∅ → A = (∅ : Set X) := by
  intro hP1 hIntEq
  -- First, deduce `A ⊆ ∅` from `P1 A` and the hypothesis on the interior.
  have hSub : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hxA
    have : (x : X) ∈ closure (interior A) := hP1 hxA
    simpa [hIntEq, closure_empty] using this
  -- The reverse inclusion is trivial.
  have hSub' : (∅ : Set X) ⊆ (A : Set X) := by
    intro x hx
    cases hx
  exact Set.Subset.antisymm hSub hSub'