

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝔄 : Set (Set X)}
    (hA : ∀ A, A ∈ 𝔄 → Topology.P2 A) :
    Topology.P2 (⋃₀ 𝔄) := by
  -- First, extract `P1` and `P3` for every member of `𝔄` from the given `P2`.
  have hP1 : ∀ A, A ∈ 𝔄 → Topology.P1 A := by
    intro A hA_mem
    exact Topology.P2_implies_P1 (hA A hA_mem)
  have hP3 : ∀ A, A ∈ 𝔄 → Topology.P3 A := by
    intro A hA_mem
    exact Topology.P2_implies_P3 (hA A hA_mem)
  -- Use the existing `sUnion` lemmas for `P1` and `P3`.
  have hP1_sUnion : Topology.P1 (⋃₀ 𝔄) := Topology.P1_sUnion hP1
  have hP3_sUnion : Topology.P3 (⋃₀ 𝔄) := Topology.P3_sUnion hP3
  -- Combine them to obtain `P2` for the union.
  exact Topology.P2_of_P1_and_P3 (A := ⋃₀ 𝔄) ⟨hP1_sUnion, hP3_sUnion⟩