

theorem Topology.not_P1_of_empty_interior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hInt : interior A = (∅ : Set X)) (hNon : A.Nonempty) :
    ¬ Topology.P1 (A := A) := by
  intro hP1
  rcases hNon with ⟨x, hxA⟩
  have hx : x ∈ closure (interior A) := hP1 hxA
  have : x ∈ (∅ : Set X) := by
    simpa [hInt, closure_empty] using hx
  cases this