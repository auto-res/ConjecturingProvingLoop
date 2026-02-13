

theorem P123_sUnion {X : Type*} [TopologicalSpace X] {𝔄 : Set (Set X)}
    (hA : ∀ A, A ∈ 𝔄 → Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) :
    Topology.P1 (⋃₀ 𝔄) ∧ Topology.P2 (⋃₀ 𝔄) ∧ Topology.P3 (⋃₀ 𝔄) := by
  -- Extract each component property for every `A ∈ 𝔄`.
  have hP1 : ∀ A, A ∈ 𝔄 → Topology.P1 A := fun A h => (hA A h).1
  have hP2 : ∀ A, A ∈ 𝔄 → Topology.P2 A := fun A h => (hA A h).2.1
  have hP3 : ∀ A, A ∈ 𝔄 → Topology.P3 A := fun A h => (hA A h).2.2
  -- Apply the existing `sUnion` lemmas for each property.
  have hP1s : Topology.P1 (⋃₀ 𝔄) := Topology.P1_sUnion hP1
  have hP2s : Topology.P2 (⋃₀ 𝔄) := Topology.P2_sUnion hP2
  have hP3s : Topology.P3 (⋃₀ 𝔄) := Topology.P3_sUnion hP3
  exact ⟨hP1s, hP2s, hP3s⟩