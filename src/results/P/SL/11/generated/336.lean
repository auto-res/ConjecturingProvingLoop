

theorem P2_sUnion_open {X : Type*} [TopologicalSpace X] {𝔄 : Set (Set X)}
    (hA : ∀ A, A ∈ 𝔄 → IsOpen (A : Set X)) :
    Topology.P2 (⋃₀ 𝔄) := by
  -- Every open set satisfies `P2`.
  have hP2 : ∀ A, A ∈ 𝔄 → Topology.P2 A := by
    intro A hA_mem
    exact Topology.P2_of_open (A := A) (hA A hA_mem)
  -- Apply the existing `sUnion` lemma for `P2`.
  exact Topology.P2_sUnion hP2