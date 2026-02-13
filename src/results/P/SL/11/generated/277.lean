

theorem P1_sUnion_open {X : Type*} [TopologicalSpace X] {𝔄 : Set (Set X)}
    (hA : ∀ A, A ∈ 𝔄 → IsOpen A) :
    Topology.P1 (⋃₀ 𝔄) := by
  -- First, produce `P1` for every member of `𝔄` using openness.
  have hP1 : ∀ A, A ∈ 𝔄 → Topology.P1 A := by
    intro A hA_mem
    exact Topology.P1_of_open (A := A) (hA A hA_mem)
  -- Apply the existing `sUnion` lemma for `P1`.
  exact Topology.P1_sUnion hP1