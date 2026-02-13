

theorem Topology.not_P2_of_empty_interior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hInt : interior A = (∅ : Set X)) (hNon : A.Nonempty) :
    ¬ Topology.P2 (A := A) := by
  intro hP2
  rcases hNon with ⟨x, hxA⟩
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  have : x ∈ (∅ : Set X) := by
    simpa [hInt, closure_empty, interior_empty] using hx
  cases this