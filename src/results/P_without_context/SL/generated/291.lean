

theorem P2_implies_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  have hP1 : Topology.P1 A := by
    dsimp [Topology.P1]
    intro x hxA
    have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
    have hsubset : interior (closure (interior A)) ⊆ closure (interior A) := by
      simpa using interior_subset (s := closure (interior A))
    exact hsubset hxInt
  have hP3 : Topology.P3 A := by
    dsimp [Topology.P3]
    intro x hxA
    have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
    have hcl_mono : closure (interior A) ⊆ closure A := by
      have hsubset : interior A ⊆ A := by
        simpa using interior_subset (s := A)
      exact closure_mono hsubset
    have hint_mono : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono hcl_mono
    exact hint_mono hxInt
  exact And.intro hP1 hP3