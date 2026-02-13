

theorem Topology.nonempty_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) → A.Nonempty → (interior A).Nonempty := by
  intro hP1 hANon
  by_contra hInt
  have hIntEq : interior A = (∅ : Set X) :=
    (Set.not_nonempty_iff_eq_empty).1 hInt
  rcases hANon with ⟨x, hxA⟩
  have hx : x ∈ closure (interior A) := hP1 hxA
  have : x ∈ (∅ : Set X) := by
    simpa [hIntEq, closure_empty] using hx
  cases this