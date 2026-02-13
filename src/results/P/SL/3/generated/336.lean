

theorem eq_empty_of_P1_and_empty_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A : Set X) →
      interior (A : Set X) = (∅ : Set X) →
      A = (∅ : Set X) := by
  intro hP1 hIntEmpty
  ext x
  constructor
  · intro hxA
    have h : (x : X) ∈ closure (interior (A : Set X)) := hP1 hxA
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [hIntEmpty, closure_empty] using h
    exact this
  · intro hxEmpty
    cases hxEmpty