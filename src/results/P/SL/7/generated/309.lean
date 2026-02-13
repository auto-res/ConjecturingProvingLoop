

theorem Topology.P2_subset_interiorClosure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hP2A : Topology.P2 A) :
    A ⊆ interior (closure B) := by
  intro x hxA
  -- From `P2 A` we know `x ∈ interior (closure (interior A))`.
  have hx₁ : x ∈ interior (closure (interior A)) := hP2A hxA
  -- Step 1: `interior (closure (interior A)) ⊆ interior (closure A)`.
  have hStep1 :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    Topology.interiorClosureInterior_subset_interiorClosure (A := A)
  -- Step 2: monotonicity under `A ⊆ B`.
  have hStep2 :
      interior (closure A) ⊆ interior (closure B) :=
    interior_mono (closure_mono hAB)
  -- Chain the inclusions to place `x` in `interior (closure B)`.
  exact hStep2 (hStep1 hx₁)