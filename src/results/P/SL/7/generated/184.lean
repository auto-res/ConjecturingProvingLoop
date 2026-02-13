

theorem Topology.P2_subset_interiorClosureInterior_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hP2A : Topology.P2 A) :
    A ⊆ interior (closure (interior B)) := by
  intro x hxA
  -- From `P2 A` we have `x ∈ interior (closure (interior A))`.
  have hxIntA : x ∈ interior (closure (interior A)) := hP2A hxA
  -- Monotonicity under the inclusion `A ⊆ B`.
  have hMonotone :
      interior (closure (interior A)) ⊆ interior (closure (interior B)) :=
    Topology.interiorClosureInterior_mono hAB
  exact hMonotone hxIntA