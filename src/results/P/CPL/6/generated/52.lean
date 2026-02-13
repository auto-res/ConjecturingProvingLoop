

theorem P3_union_sUnion {X : Type*} [TopologicalSpace X] {𝓢 : Set (Set X)} {B : Set X} : (∀ A ∈ 𝓢, Topology.P3 A) → Topology.P3 B → Topology.P3 (B ∪ ⋃₀ 𝓢) := by
  intro hP3S hP3B
  have hP3_sUnion : Topology.P3 (⋃₀ 𝓢) := by
    apply P3_sUnion (X := X) (𝓢 := 𝓢)
    exact hP3S
  exact P3_union (A := B) (B := ⋃₀ 𝓢) hP3B hP3_sUnion

theorem P3_of_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed (Aᶜ)) : Topology.P3 A := by
  have hOpen : IsOpen (A : Set X) := by
    simpa using hA.isOpen_compl
  exact P3_of_open (A := A) hOpen