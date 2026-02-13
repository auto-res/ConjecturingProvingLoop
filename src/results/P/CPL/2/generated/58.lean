

theorem P2_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (A : Set X) : Topology.P2 (X:=X) A := by
  classical
  -- Unfold the definition of `P2`
  unfold Topology.P2
  intro x hx
  -- In a discrete topology every set is open
  have hA_open : IsOpen (A : Set X) := by
    simpa using (isOpen_discrete (s := A))
  -- Hence `interior A = A`
  have hInt : interior A = A := hA_open.interior_eq
  -- View `hx` as a membership in `interior A`
  have hxInt : x ∈ interior A := by
    simpa [hInt] using hx
  -- Use monotonicity of `interior`
  have h_subset :
      (interior A : Set X) ⊆ interior (closure (interior A)) := by
    simpa using
      (interior_mono
        (subset_closure : (interior A : Set X) ⊆ closure (interior A)))
  exact h_subset hxInt

theorem P1_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {U : Set Y} (hU : IsOpen U) : Topology.P1 (X:=X) (f ⁻¹' U) := by
  -- `f ⁻¹' U` is open since `f` is continuous and `U` is open
  have hOpen : IsOpen (f ⁻¹' U) := hU.preimage hf
  -- apply the lemma for open sets
  exact P1_of_open (X := X) (A := f ⁻¹' U) hOpen